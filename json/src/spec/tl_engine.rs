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

//! Authority params deserialization.

use ethereum_types::Address;
use uint::Uint;
use super::ValidatorSet;

/// Authority params deserialization.
#[derive(Debug, PartialEq, Deserialize)]
pub struct TLEngineParams {
	pub value: Option<Uint>,
}

/// Authority engine deserialization.
#[derive(Debug, PartialEq, Deserialize)]
pub struct TLEngine {
	/// Ethash params.
	pub params: TLEngineParams,
}

#[cfg(test)]
mod tests {
	use ethereum_types::{U256, H160};
	use uint::Uint;
	use serde_json;
	use hash::Address;
	use spec::tl_engine::TLEngine;

	#[test]
	fn authority_round_deserialization() {
		let s = r#"{
			"params": {
				"value": 1
			}
		}"#;

		let deserialized: TLEngine = serde_json::from_str(s).unwrap();
		assert_eq!(deserialized.params.value, Some(Uint(1.into())));

	}
}
