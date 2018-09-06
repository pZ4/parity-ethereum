// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

//! A blockchain engine that supports a non-instant BFT proof-of-authority.

use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::iter::FromIterator;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering as AtomicOrdering};
use std::sync::{Weak, Arc};
use std::time::{UNIX_EPOCH, SystemTime, Duration};

use account_provider::AccountProvider;
use block::*;
use client::EngineClient;
use engines::{Engine, Seal, EngineError, ConstructedVerifier};
use engines::block_reward;
use engines::block_reward::{BlockRewardContract, RewardKind};
use error::{Error, ErrorKind, BlockError};
use ethjson;
use machine::{AuxiliaryData, Call, EthereumMachine};
use hash::keccak;
use header::{Header, BlockNumber, ExtendedHeader};
use super::signer::EngineSigner;
use super::validator_set::{ValidatorSet, SimpleList, new_validator_set};
use self::finality::RollingFinality;
use ethkey::{self, Password, Signature};
use io::{IoContext, IoHandler, TimerToken, IoService};
use itertools::{self, Itertools};
use rlp::{encode, Decodable, DecoderError, Encodable, RlpStream, Rlp};
use ethereum_types::{H256, H520, Address, U128, U256};
use parking_lot::{Mutex, RwLock};
use unexpected::{Mismatch, OutOfBounds};

mod finality;

/// `TLEngine` params.
pub struct TLEngineParams {
	/// Time to wait before next block or authority switching,
	/// in seconds.
	///
	/// Deliberately typed as u16 as too high of a value leads
	/// to slow block issuance.
	pub step_duration: u16,
	/// Starting step,
	pub start_step: Option<u64>,
	/// Valid validators.
	pub validators: Box<ValidatorSet>,
	/// Chain score validation transition block.
	pub validate_score_transition: u64,
	/// Monotonic step validation transition block.
	pub validate_step_transition: u64,
	/// Immediate transitions.
	pub immediate_transitions: bool,
	/// Block reward in base units.
	pub block_reward: U256,
	/// Block reward contract transition block.
	pub block_reward_contract_transition: u64,
	/// Block reward contract.
	pub block_reward_contract: Option<BlockRewardContract>,
	/// Number of accepted uncles transition block.
	pub maximum_uncle_count_transition: u64,
	/// Number of accepted uncles.
	pub maximum_uncle_count: usize,
	/// Empty step messages transition block.
	pub empty_steps_transition: u64,
	/// Number of accepted empty steps.
	pub maximum_empty_steps: usize,
}

const U16_MAX: usize = ::std::u16::MAX as usize;

impl From<ethjson::spec::TLEngineParams> for TLEngineParams {
	fn from(p: ethjson::spec::TLEngineParams) -> Self {
		let mut step_duration_usize: usize = p.step_duration.into();
		if step_duration_usize > U16_MAX {
			step_duration_usize = U16_MAX;
			warn!(target: "engine", "step_duration is too high ({}), setting it to {}", step_duration_usize, U16_MAX);
		}
		TLEngineParams {
			step_duration: step_duration_usize as u16,
			validators: new_validator_set(p.validators),
			start_step: p.start_step.map(Into::into),
			validate_score_transition: p.validate_score_transition.map_or(0, Into::into),
			validate_step_transition: p.validate_step_transition.map_or(0, Into::into),
			immediate_transitions: p.immediate_transitions.unwrap_or(false),
			block_reward: p.block_reward.map_or_else(Default::default, Into::into),
			block_reward_contract_transition: p.block_reward_contract_transition.map_or(0, Into::into),
			block_reward_contract: p.block_reward_contract_address.map(BlockRewardContract::new),
			maximum_uncle_count_transition: p.maximum_uncle_count_transition.map_or(0, Into::into),
			maximum_uncle_count: p.maximum_uncle_count.map_or(0, Into::into),
			empty_steps_transition: p.empty_steps_transition.map_or(u64::max_value(), |n| ::std::cmp::max(n.into(), 1)),
			maximum_empty_steps: p.maximum_empty_steps.map_or(0, Into::into),
		}
	}
}

#[derive(Debug)]
struct SimpleMessage {
	signature: H520,
	value: u64,
}

impl Decodable for SimpleMessage {
	fn decode(rlp: &Rlp) -> Result<Self, DecoderError> {
		let list = rlp.at(0)?;
		let signature = list.val_at(0)?;
		let value = list.val_at(1)?;

		Ok(SimpleMessage { signature, value })
	}
}

impl Encodable for SimpleMessage {
	fn rlp_append(&self, s: &mut RlpStream) {
		s.begin_list(2)
			.append(&self.signature)
			.append(&self.value);
	}
}

/// Engine using `TLEngine` proof-of-authority BFT consensus.
pub struct TLEngine {
	transition_service: IoService<()>,
	client: Arc<RwLock<Option<Weak<EngineClient>>>>,
	signer: RwLock<EngineSigner>,
	validators: Box<ValidatorSet>,
	validate_score_transition: u64,
	validate_step_transition: u64,
	immediate_transitions: bool,
	block_reward: U256,
	block_reward_contract_transition: u64,
	block_reward_contract: Option<BlockRewardContract>,
	maximum_uncle_count_transition: u64,
	maximum_uncle_count: usize,
	empty_steps_transition: u64,
	maximum_empty_steps: usize,
	machine: EthereumMachine,
}


impl TLEngine {
	/// Create a new instance of TLEngine engine.
	pub fn new(our_params: TLEngineParams, machine: EthereumMachine) -> Result<Arc<Self>, Error> {
		if our_params.step_duration == 0 {
			error!(target: "engine", "Authority Round step duration can't be zero, aborting");
			panic!("authority_round: step duration can't be zero")
		}
		let should_timeout = our_params.start_step.is_none();
		let engine = Arc::new(
			TLEngine {
				transition_service: IoService::<()>::start()?,
				client: Arc::new(RwLock::new(None)),
				signer: Default::default(),
				validators: our_params.validators,
				validate_score_transition: our_params.validate_score_transition,
				validate_step_transition: our_params.validate_step_transition,
				immediate_transitions: our_params.immediate_transitions,
				block_reward: our_params.block_reward,
				block_reward_contract_transition: our_params.block_reward_contract_transition,
				block_reward_contract: our_params.block_reward_contract,
				maximum_uncle_count_transition: our_params.maximum_uncle_count_transition,
				maximum_uncle_count: our_params.maximum_uncle_count,
				empty_steps_transition: our_params.empty_steps_transition,
				maximum_empty_steps: our_params.maximum_empty_steps,
				machine: machine,
			});

		// Do not initialize timeouts for tests.
		if should_timeout {
			let handler = TransitionHandler {
				client: engine.client.clone(),
			};
			engine.transition_service.register_handler(Arc::new(handler))?;
		}
		Ok(engine)
	}

	fn broadcast_message(&self, message: Vec<u8>) {
		println!("Broadcasting message {:?}", message);
		if let Some(ref weak) = *self.client.read() {
			if let Some(c) = weak.upgrade() {
				c.broadcast_consensus_message(message);
			}
		}
	}
}


struct TransitionHandler {
	client: Arc<RwLock<Option<Weak<EngineClient>>>>,
}

const ENGINE_TIMEOUT_TOKEN: TimerToken = 23;

impl IoHandler<()> for TransitionHandler {
	fn initialize(&self, io: &IoContext<()>) {
		let remaining = 2000;
		io.register_timer_once(ENGINE_TIMEOUT_TOKEN, Duration::from_millis(remaining))
			.unwrap_or_else(|e| warn!(target: "engine", "Failed to start consensus step timer: {}.", e))
	}

	fn timeout(&self, io: &IoContext<()>, timer: TimerToken) {
		if timer == ENGINE_TIMEOUT_TOKEN {
			// NOTE we might be lagging by couple of steps in case the timeout
			// has not been called fast enough.
			// Make sure to advance up to the actual step.

			let next_run_at = 2000 >> 2;
			io.register_timer_once(ENGINE_TIMEOUT_TOKEN, Duration::from_millis(next_run_at))
				.unwrap_or_else(|e| warn!(target: "engine", "Failed to restart consensus step timer: {}.", e))
		}
	}
}

impl Engine<EthereumMachine> for TLEngine{

	fn name(&self) -> &str { "TLEngine" }

	fn machine(&self) -> &EthereumMachine { &self.machine }

	fn verify_local_seal(&self, _header: &Header) -> Result<(), Error> { Ok(()) }

	fn fork_choice(&self, new: &ExtendedHeader, current: &ExtendedHeader) -> super::ForkChoice {
		super::total_difficulty_fork_choice(new, current)
	}

	fn seals_internally(&self) -> Option<bool> {Some(true) }

	fn generate_seal(&self, block: &ExecutedBlock, _parent: &Header) -> Seal {
		//custom to send message
		{
			let message = SimpleMessage{value: 12, signature: H520::default()};
			println!("Sending message {:?}", message);
			let mut s = RlpStream::new_list(1);
			s.append(&message);
			let rlp_message = s.out();
			self.broadcast_message(rlp_message);
		}
		if block.transactions().is_empty() { Seal::None } else { Seal::Regular(Vec::new()) }
	}

	fn open_block_header_timestamp(&self, parent_timestamp: u64) -> u64 {
		use std::{time, cmp};

		let now = time::SystemTime::now().duration_since(time::UNIX_EPOCH).unwrap_or_default();
		cmp::max(now.as_secs(), parent_timestamp)
	}

	fn is_timestamp_valid(&self, header_timestamp: u64, parent_timestamp: u64) -> bool {
		header_timestamp >= parent_timestamp
	}

	/// necessary in order to receive messages
	fn register_client(&self, client: Weak<EngineClient>) {
		*self.client.write() = Some(client.clone());
	}

	/// necessary in order to receive messages
	fn handle_message(&self, rlp: &[u8]) -> Result<(), EngineError> {
		println!("handle_message");
		fn fmt_err<T: ::std::fmt::Debug>(x: T) -> EngineError {
			println!("malformed message");
			EngineError::MalformedMessage(format!("{:?}", x))
		}

		let rlp = Rlp::new(rlp);
		let simpleMessage: SimpleMessage = rlp.as_val().map_err(fmt_err)?;
		println!("Message received {:?}", simpleMessage);

		Ok(())
	}

	fn step(&self) {
		println!("step");
	}
}

#[cfg(test)]
mod tests {
}
