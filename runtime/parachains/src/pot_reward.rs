// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Pot Reward Pallet
//!
//! - [`Config`]
//! - [`Call`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The Pot Reward Pallet is a pallet that rewards validators
//! who are selected due to pot consensus.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use std::collections::HashMap;

use frame_support::{
	dispatch::{DispatchInfo, DispatchResult, PostDispatchInfo},
	pallet_prelude::*,
	traits::{
		tokens::{
			fungibles::{Balanced, CreditOf, Inspect},
			AssetId, Balance, WithdrawConsequence,
		},
		IsType, ValidatorSet, ValidatorSetWithIdentification,
	},
	DefaultNoBound,
};
use frame_system::pallet_prelude::*;
use log::{debug, error, info, trace, warn};
use pallet_session::historical;
use primitives::AccountId;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{Convert, StaticLookup},
	RuntimeDebug,
};
use sp_staking::SessionIndex;
use sp_std::prelude::*;

pub use pallet::*;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

/// A type for representing the validator id in a session.
pub type ValidatorId<T> = <<T as Config>::ValidatorSet as ValidatorSet<
	<T as frame_system::Config>::AccountId,
>>::ValidatorId;

#[derive(Encode, Decode, Clone, PartialEq, Eq, sp_core::RuntimeDebug, TypeInfo)]
pub struct ValidatorReward {
	#[codec(compact)]
	pub asset_id: u32,
	#[codec(compact)]
	pub amount: u128,
}

impl ValidatorReward {
	pub fn new(asset_id: u32, amount: u128) -> Self {
		Self { asset_id, amount }
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// A type for retrieving the validators supposed to be online in a session.
		type ValidatorSet: ValidatorSet<Self::AccountId>;
	}

	#[pallet::storage]
	#[pallet::getter(fn validator_rewards)]
	#[pallet::unbounded]
	pub type ValidatorRewards<T: Config> =
		StorageMap<_, Twox64Concat, ValidatorId<T>, Vec<ValidatorReward>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The validator has been rewarded.
		Rewarded { stash: ValidatorId<T> },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Not a controller account.
		NotController,
		/// Rewards already been claimed for this validator.
		AlreadyClaimed,
		NothingToClaim,
		NeedOriginSignature,
		NoAssociatedValidatorId,
		Unknown,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn claim(origin: OriginFor<T>, controller: AccountIdLookupOf<T>) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let controller = T::Lookup::lookup(controller)?;
			ensure!(origin == controller, Error::<T>::NeedOriginSignature);
			let who = <T::ValidatorSet as ValidatorSet<T::AccountId>>::ValidatorIdOf::convert(
				controller.clone(),
			)
			.ok_or(Error::<T>::NoAssociatedValidatorId)?;
			ensure!(ValidatorRewards::<T>::contains_key(who.clone()), Error::<T>::NothingToClaim);
			let mut rewards: Vec<ValidatorReward> =
				ValidatorRewards::<T>::get(who.clone()).unwrap();
			ensure!(rewards.len() != 0, Error::<T>::AlreadyClaimed);
			for reward in rewards.iter_mut() {
				// TODO: send asset to validator with DMP
				reward.amount = 0;
			}
			rewards.retain(|r| r.amount != 0);
			ValidatorRewards::<T>::remove(who.clone());
			ValidatorRewards::<T>::insert(who.clone(), rewards);

			Self::deposit_event(Event::Rewarded { stash: who.into() });
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	fn new_session(_new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		None
	}
	fn new_session_genesis(_new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		None
	}
	fn start_session(_start_index: SessionIndex) {}
	fn end_session(_end_index: SessionIndex) {
		let current_validators = T::ValidatorSet::validators();
		// TODO: need to change "real" system token
		let system_token_set = HashMap::from([(1, 100), (2, 200), (3, 150)]);
		for validator in current_validators.iter() {
			if ValidatorRewards::<T>::contains_key(validator) {
				let _ = ValidatorRewards::<T>::try_mutate_exists(
					validator,
					|maybe_rewards| -> Result<(), DispatchError> {
						let rewards = maybe_rewards.as_mut().ok_or(Error::<T>::Unknown)?;
						for reward in rewards.iter_mut() {
							let amount = *system_token_set.get(&reward.asset_id).unwrap_or(&0) /
								current_validators.len() as u128;
							reward.amount += amount;
						}
						Ok(())
					},
				);
			} else {
				// TODO: need to change "real" system token
				let rewards = {
					let mut rewards = Vec::new();
					for system_token in system_token_set.iter() {
						rewards.push(ValidatorReward::new(*system_token.0, *system_token.1));
					}
					rewards
				};
				ValidatorRewards::<T>::insert(validator, rewards);
			}
		}
	}
}

/// In this implementation `new_session(session)` must be called before `end_session(session-1)`
/// i.e. the new session must be planned before the ending of the previous session.
///
/// Once the first new_session is planned, all session must start and then end in order, though
/// some session can lag in between the newest session planned and the latest session started.
impl<T: Config> pallet_session::SessionManager<T::AccountId> for Pallet<T> {
	fn new_session(new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		info!("🏁 planning new session {}", new_index);
		Self::new_session(new_index)
	}
	fn new_session_genesis(new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		info!("🏁 planning new session {} at genesis", new_index);
		Self::new_session(new_index)
	}
	fn start_session(start_index: SessionIndex) {
		info!("🏁 starting session {}", start_index);
		Self::start_session(start_index)
	}
	fn end_session(end_index: SessionIndex) {
		info!("🏁 ending session {}", end_index);
		Self::end_session(end_index)
	}
}
