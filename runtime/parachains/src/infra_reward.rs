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

use frame_support::{
	dispatch::DispatchResult,
	pallet_prelude::*,
	traits::{IsType, ValidatorSet},
	PalletId,
};
use frame_system::pallet_prelude::*;
use primitives::Id as ParaId;
use scale_info::TypeInfo;
use sp_runtime::{
	generic::{VoteAssetId, VoteWeight},
	traits::{AccountIdConversion, Convert, StaticLookup},
};
use sp_std::prelude::*;
use pallet_infra_voting::{RewardInterface, SessionIndex};
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
	use crate::{configuration, dmp, paras};

	use super::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

	#[pallet::pallet]
	#[pallet::without_storage_info]
	#[pallet::generate_store(pub(crate) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ configuration::Config
		+ paras::Config
		+ dmp::Config
		+ pallet_assets::Config
	{
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

	#[pallet::storage]
	#[pallet::getter(fn session_rewards)]
	#[pallet::unbounded]
	pub type TotalSessionRewards<T: Config> =
		StorageMap<_, Twox64Concat, SessionIndex, Vec<ValidatorReward>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The validator has been rewarded.
		Rewarded { stash: ValidatorId<T>, asset_id: T::AssetId, amount: u128 },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Not a controller account.
		NotController,
		/// Rewards already been claimed for this validator.
		AlreadyClaimed,
		EmptyAggregatedRewards,
		NothingToClaim,
		NeedOriginSignature,
		NoAssociatedValidatorId,
		ExceedsMaxMessageSize,
		Unknown,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		u32: PartialEq<<T as pallet_assets::Config>::AssetId>,
		<T as pallet_assets::Config>::Balance: From<u128>,
	{
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn claim(
			origin: OriginFor<T>,
			controller: AccountIdLookupOf<T>,
			asset_id: T::AssetIdParameter,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let validator = T::Lookup::lookup(controller.clone())?;
			let id: T::AssetId = asset_id.into();

			ensure!(origin == validator, Error::<T>::NeedOriginSignature);

			let who = <T::ValidatorSet as ValidatorSet<T::AccountId>>::ValidatorIdOf::convert(
				validator.clone(),
			)
			.ok_or(Error::<T>::NoAssociatedValidatorId)?;
			ensure!(ValidatorRewards::<T>::contains_key(who.clone()), Error::<T>::NothingToClaim);
			let mut rewards: Vec<ValidatorReward> =
				ValidatorRewards::<T>::get(who.clone()).unwrap_or_default();
			ensure!(rewards.len() != 0, Error::<T>::NothingToClaim);

			let sovereign = Self::account_id();
			if let Some(reward) = rewards.iter_mut().find(|ar| ar.asset_id == id) {
				let config = <configuration::Pallet<T>>::config();
				let xcm = {
					use parity_scale_codec::Encode as _;
					use xcm::opaque::{latest::prelude::*, VersionedXcm};

					let mut encoded: Vec<u8> = [0x32].into(); // asset pallet number
					let mut call_encode: Vec<u8> = pallet_assets::Call::<T>::force_transfer2 {
						id: asset_id,
						source: T::Lookup::unlookup(sovereign.clone()),
						dest: controller.clone(),
						amount: <T as pallet_assets::Config>::Balance::from(reward.amount),
					}
					.encode();

					encoded.append(&mut call_encode);

					let fee_multilocation =
						MultiAsset { id: Concrete(Here.into()), fun: Fungible(10000) };

					VersionedXcm::from(Xcm(vec![
						BuyExecution {
							fees: fee_multilocation.clone().into(),
							weight_limit: WeightLimit::Unlimited,
						},
						Transact {
							origin_kind: OriginKind::Superuser,
							require_weight_at_most: Weight::from_parts(10_000_000_000, 1_100_000),
							call: encoded.into(),
						},
					]))
					.encode()
				};
				if let Err(dmp::QueueDownwardMessageError::ExceedsMaxMessageSize) =
					<dmp::Pallet<T>>::queue_downward_message(&config, ParaId::from(1000_u32), xcm)
				{
					log::error!(
						target: "runtime::infra_reward",
						"sending 'dmp' failed."
					);
				};
				Self::deposit_event(Event::Rewarded {
					stash: who.into(),
					asset_id: id,
					amount: reward.amount,
				});
				reward.amount = 0;
			}

			Ok(())
		}
		#[pallet::call_index(1)]
		#[pallet::weight(0)]
		pub fn test(
			origin: OriginFor<T>,
			controller: AccountIdLookupOf<T>,
			asset_id: u32,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let validator = T::Lookup::lookup(controller.clone())?;
			let who = <T::ValidatorSet as ValidatorSet<T::AccountId>>::ValidatorIdOf::convert(
				validator.clone(),
			)
			.ok_or(Error::<T>::NoAssociatedValidatorId)?;

			ensure!(origin == validator, Error::<T>::NeedOriginSignature);

			let aggregated_rewards = vec![ValidatorReward::new(asset_id, 10000000)];

			let rewards: Vec<ValidatorReward> = aggregated_rewards
				.iter()
				.map(|reward| ValidatorReward::new(reward.asset_id, reward.amount))
				.collect();
			ValidatorRewards::<T>::insert(who, rewards);

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	pub fn account_id() -> T::AccountId {
		let pallet_id = PalletId(*b"infrafee");
		pallet_id.into_account_truncating()
	}

	fn aggregate_reward(session_index: SessionIndex, asset_id: VoteAssetId, amount: VoteWeight) {
		let asset_id: u32 = asset_id.into();
		let amount: u128 = amount.into();

		if let Some(rewards) = TotalSessionRewards::<T>::get(session_index) {
			for reward in rewards.clone().iter_mut().filter(|r| r.asset_id == asset_id) {
				reward.amount += amount;
			}
		} else {
			let rewards = vec![ValidatorReward::new(asset_id, amount)];
			TotalSessionRewards::<T>::insert(session_index, rewards);
		}
	}
	fn distribute_reward(session_index: SessionIndex) {
		let current_validators = T::ValidatorSet::validators();
		let aggregated_rewards = TotalSessionRewards::<T>::get(session_index).unwrap_or_default();

		for validator in current_validators.iter() {
			if ValidatorRewards::<T>::contains_key(validator) {
				let _ = ValidatorRewards::<T>::try_mutate_exists(
					validator,
					|maybe_rewards| -> Result<(), DispatchError> {
						let rewards = maybe_rewards.as_mut().ok_or(Error::<T>::Unknown)?;
						for reward in rewards.iter_mut() {
							if let Some(aggregated_reward) =
								aggregated_rewards.iter().find(|ar| ar.asset_id == reward.asset_id)
							{
								let amount =
									aggregated_reward.amount / current_validators.len() as u128;
								reward.amount += amount;
							}
						}
						Ok(())
					},
				);
			} else {
				let rewards: Vec<ValidatorReward> = aggregated_rewards
					.iter()
					.map(|reward| {
						ValidatorReward::new(
							reward.asset_id,
							reward.amount / current_validators.len() as u128,
						)
					})
					.collect();
				ValidatorRewards::<T>::insert(validator, rewards);
			}
		}
	}
}

impl<T: Config> RewardInterface for Pallet<T> {
	fn aggregate_reward(session_index: SessionIndex, asset_id: VoteAssetId, amount: VoteWeight) {
		Self::aggregate_reward(session_index, asset_id, amount);
	}

	fn distribute_reward(session_index: SessionIndex) {
		Self::distribute_reward(session_index);
	}
}
