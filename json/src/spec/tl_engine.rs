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

//! Null engine params deserialization.

use uint::Uint;

/// Authority params deserialization.
#[derive(Debug, PartialEq, Deserialize)]
pub struct TLEngineParams {
	/// Block reward.
	#[serde(rename="unused")]
	pub _unused: Option<i64>,
}

/// TL engine descriptor
#[derive(Debug, PartialEq, Deserialize)]
pub struct TLEngine {
	/// Ethash params.
	pub params: TLEngineParams,
}

#[cfg(test)]
mod tests {
	use serde_json;
	use uint::Uint;
	use ethereum_types::U256;
	use super::*;

	#[test]
	fn tl_engine_deserialization() {
		let s = r#"{
			"params": {
				"unused": "1"
			}
		}"#;

		let deserialized: TLEngine = serde_json::from_str(s).unwrap();
		assert_eq!(deserialized.params._unused, Some(1));
	}
}
