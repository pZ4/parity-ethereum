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


use error::Error;
use ethereum_types::U256;
use engines::Engine;
use engines::block_reward::{self, RewardKind};
use header::{Header, ExtendedHeader, BlockNumber};
use machine::{EthereumMachine};

/// Params for a null engine.
#[derive(Clone, Default)]
pub struct TLEngineParams {
	/// base reward for a block.
	pub block_reward: U256,
}

impl From<::ethjson::spec::TLEngineParams> for TLEngineParams {
	fn from(p: ::ethjson::spec::TLEngineParams) -> Self {
		TLEngineParams {
			block_reward: p.block_reward.map_or_else(Default::default, Into::into),
		}
	}
}

/// An engine which does not provide any consensus mechanism and does not seal blocks.
pub struct TLEngine {
	params: TLEngineParams,
	machine: EthereumMachine,
}

impl TLEngine {
	/// Returns new instance of TLEngine with default VM Factory
	pub fn new(params: TLEngineParams, machine: EthereumMachine) -> Self {
		TLEngine {
			params: params,
			machine: machine,
		}
	}
}

// see https://github.com/paritytech/parity-ethereum/blob/master/ethcore/src/engines/mod.rs#L195
// to check what does what
impl Engine<EthereumMachine> for TLEngine {

	/// The name of this engine.
	fn name(&self) -> &str {
		"TLEngine"
	}

	/// Get access to the underlying state machine.
	fn machine(&self) -> &EthereumMachine { &self.machine }

	fn fork_choice(&self, new: &ExtendedHeader, current: &ExtendedHeader) -> super::ForkChoice {
		super::total_difficulty_fork_choice(new, current)
	}

	fn verify_local_seal(&self, _header: &Header) -> Result<(), Error> {
		Ok(())
	}
}
