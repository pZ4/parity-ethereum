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

//! An instant sealing consensus that gossips each time a block is sealed.

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
use ethkey::{self, Password, Signature};
use io::{IoContext, IoHandler, TimerToken, IoService};
use itertools::{self, Itertools};
use rlp::{encode, Decodable, DecoderError, Encodable, RlpStream, Rlp};
use ethereum_types::{H256, H520, Address, U128, U256};
use parking_lot::{Mutex, RwLock};
use unexpected::{Mismatch, OutOfBounds};

/// `TLEngine` params.
pub struct TLEngineParams {
	pub value: u64,
	pub validators: BTreeMap<String, f64>,
}

impl From<ethjson::spec::TLEngineParams> for TLEngineParams {
	fn from(p: ethjson::spec::TLEngineParams) -> Self {
		TLEngineParams {
			value: p.value.map_or(0, Into::into),
			validators: p.validators,
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
	client: Arc<RwLock<Option<Weak<EngineClient>>>>,
	machine: EthereumMachine,
	validators: BTreeMap<String, f64>,
	value: u64,
}


impl TLEngine {
	/// Create a new instance of TLEngine engine.
	pub fn new(our_params: TLEngineParams, machine: EthereumMachine) -> Result<Arc<Self>, Error> {
		let engine = Arc::new(
			TLEngine {
				client: Arc::new(RwLock::new(None)),
				value: our_params.value,
				validators: our_params.validators,
				machine: machine,
			});

		Ok(engine)
	}

	fn broadcast_message(&self, message: Vec<u8>) {
		if let Some(ref weak) = *self.client.read() {
			if let Some(c) = weak.upgrade() {
				c.broadcast_consensus_message(message);
			}
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
			let message = SimpleMessage{value: self.value, signature: H520::default()};
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
		println!("Handling message");
		fn fmt_err<T: ::std::fmt::Debug>(x: T) -> EngineError {
			println!("Malformed message");
			EngineError::MalformedMessage(format!("{:?}", x))
		}

		let rlp = Rlp::new(rlp);
		let simple_message: SimpleMessage = rlp.as_val().map_err(fmt_err)?;
		println!("Message received {:?}", simple_message);

		Ok(())
	}
}

/// tests from the instant seal consensus
#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use ethereum_types::{H520, Address};
	use test_helpers::get_temp_state_db;
	use spec::Spec;
	use header::Header;
	use block::*;
	use engines::Seal;

	#[test]
	fn tlengine_can_seal() {
		let spec = Spec::new_tlengine();
		let engine = &*spec.engine;
		let db = spec.ensure_db_good(get_temp_state_db(), &Default::default()).unwrap();
		let genesis_header = spec.genesis_header();
		let last_hashes = Arc::new(vec![genesis_header.hash()]);
		let b = OpenBlock::new(engine, Default::default(), false, db, &genesis_header, last_hashes, Address::default(), (3141562.into(), 31415620.into()), vec![], false, &mut Vec::new().into_iter()).unwrap();
		let b = b.close_and_lock().unwrap();
		if let Seal::Regular(seal) = engine.generate_seal(b.block(), &genesis_header) {
			assert!(b.try_seal(engine, seal).is_ok());
		}
	}

	#[test]
	fn tlengine_cant_verify() {
		let engine = Spec::new_tlengine().engine;
		let mut header: Header = Header::default();

		assert!(engine.verify_block_basic(&header).is_ok());

		header.set_seal(vec![::rlp::encode(&H520::default()).into_vec()]);

		assert!(engine.verify_block_unordered(&header).is_ok());
	}
}
