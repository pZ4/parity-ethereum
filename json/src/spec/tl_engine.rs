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

use uint::Uint;
use std::collections::BTreeMap;

/// Authority params deserialization.
#[derive(Debug, PartialEq, Deserialize)]
pub struct TLEngineParams {
	pub value: Option<Uint>,
	pub validators: BTreeMap<String, f64>,
}

/// Authority engine deserialization.
#[derive(Debug, PartialEq, Deserialize)]
pub struct TLEngine {
	/// Ethash params.
	pub params: TLEngineParams,
}

#[cfg(test)]
mod tests {
	use uint::Uint;
	use serde_json;
	use spec::tl_engine::TLEngine;

	#[test]
	fn tl_params_deserialization() {
		let s = r#"{
			"params": {
				"value": 1,
				"validators": {
					"0xc6d9d2cd449a754c494264e1809c50e34d64562b": 1.2,
					"0xd6d9d2cd449a754c494264e1809c50e34d64562b": 0.2
				}
			}
		}"#;

		let deserialized: TLEngine = serde_json::from_str(s).unwrap();
		assert_eq!(deserialized.params.value, Some(Uint(1.into())));

		if let Some(weight_c) = deserialized.params.validators.get("0xc6d9d2cd449a754c494264e1809c50e34d64562b") {
			assert_eq!(*weight_c, 1.2 as f64);
		}
		else {
			panic!("Weight for 0xc6d9d2cd449a754c494264e1809c50e34d64562b not found");
		}

		if let Some(weight_d) = deserialized.params.validators.get("0xd6d9d2cd449a754c494264e1809c50e34d64562b") {
			assert_eq!(*weight_d, 0.2 as f64);
		}
		else {
			panic!("Weight for 0xd6d9d2cd449a754c494264e1809c50e34d64562b not found");
		}

		// is the "if let None" ugly?
		if let None = deserialized.params.validators.get("not found") {
			assert!(true);
		}
		else {
			panic!("Should not be able to find a validator")
		}
	}
}
