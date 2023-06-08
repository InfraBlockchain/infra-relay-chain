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

//! # Tokem manager Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! Token manager handles all infomration related with system tokens on the relay chain level.
//!
//! ### Functions
//!
//! * `set_name` - Set the associated name of an account; a small deposit is reserved if not already
//!   taken.
//! *

#![cfg_attr(not(feature = "std"), no_std)]
use frame_support::{
	pallet_prelude::{OptionQuery, *},
	PalletId,
};
pub use pallet::*;
use parity_scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime::{
	generic::{SystemTokenId, VoteAssetId, VoteWeight},
	traits::{AccountIdConversion, ConstU32, StaticLookup},
	BoundedVec, RuntimeDebug,
};
use sp_std::prelude::*;

pub type ParaAssetId = VoteAssetId;
pub type RelayAssetId = VoteAssetId;
pub type ParaId = u32;
pub type PalletIndex = u32;
pub type ExchangeRate = u32;

/// Data structure for Wrapped system tokens
pub type WrappedSystemTokenId = SystemTokenId;

type StringLimit = ConstU32<32>;
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct SystemTokenMetadata {
	/// `is_sufficient = true` should be used as a system token.
	pub is_sufficient: bool,
	/// The minimum balance of this new system token that any single account must have.
	pub min_balance: u32,
	/// The number of decimals this system token uses to represent one unit.
	pub decimal: u64,
	/// The total supply for the system token.
	pub total_supply: u64,
	/// The user friendly name of this system token.
	pub name: BoundedVec<u8, StringLimit>,
	/// The exchange symbol for this system token.
	pub symbol: BoundedVec<u8, StringLimit>,
	/// The exchange rate
	pub exchange_rate: u32,
}

impl SystemTokenMetadata {
	pub fn get_exchange_rate(&self) -> u32 {
		self.exchange_rate
	}
}

/// System tokens API.
pub trait SystemTokenInterface {
	/// Check the system token is registered.
	fn is_system_token(system_token: SystemTokenId) -> bool;
	/// Convert para system token to original system token.
	fn convert_to_original_system_token(
		wrapped_token: WrappedSystemTokenId,
	) -> Option<SystemTokenId>;
	/// Adjust the vote weight calculating exchange rate.
	fn adjusted_weight(system_token: SystemTokenId, vote_weight: VoteWeight) -> VoteWeight;
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use crate::{configuration, dmp, paras};
	use frame_system::pallet_prelude::*;

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
		/// The string limit for name and symbol of system token.
		#[pallet::constant]
		type StringLimit: Get<u32>;
		/// Max number which can be used as system tokens on parachain.
		#[pallet::constant]
		type MaxWrappedSystemToken: Get<u32>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Register a new system token.
		SystemTokenRegistered {
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		},
		// Remove the system token.
		SystemTokenRemoved {
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		},
		// Convert a wrapped system token id to an original system token id.
		SystemTokenConverted {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Failed to register a system token as it is already registered.
		SystemTokenAlreadyRegistered,
		/// Failed to remove the system token as it is not registered.
		SystemTokenNotRegistered,
		WrappedSystemTokenAlreadyRegistered,
		WrongSystemTokenMetadata,
		Unknown,
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	#[pallet::getter(fn system_token_list)]
	/// List for original system token and metadata.
	pub(super) type SystemTokenList<T: Config> =
		StorageMap<_, Twox64Concat, SystemTokenId, SystemTokenMetadata, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn system_token_on_parachain)]
	/// Coverter between WrappedSystemTokenId and original SystemTokenId.
	pub(super) type SystemTokenOnParachain<T: Config> =
		StorageMap<_, Twox64Concat, WrappedSystemTokenId, SystemTokenId, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn system_token_on_parachain_by_para_id)]
	/// System token list for specific parachain by ParaId.
	pub(super) type SystemTokenOnParachainByParaId<T: Config> = StorageMap<
		_,
		Twox64Concat,
		ParaId,
		BoundedVec<WrappedSystemTokenId, T::MaxWrappedSystemToken>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn allowed_system_token)]
	/// Wrapped System token list used in parachains.
	pub(super) type AllowedSystemToken<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		PalletIndex,
		Twox64Concat,
		ParaAssetId,
		WrappedSystemTokenId,
		OptionQuery,
	>;

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		u32: PartialEq<<T as pallet_assets::Config>::AssetId>,
		<T as pallet_assets::Config>::Balance: From<u128>,
		<T as pallet_assets::Config>::AssetIdParameter: From<u32>,
	{
		/// Register a system token.
		#[pallet::call_index(0)]
		#[pallet::weight(1_000)]
		pub fn register_system_token(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				!SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenAlreadyRegistered
			);
			ensure!(system_token_metadata.is_sufficient, Error::<T>::WrongSystemTokenMetadata);

			SystemTokenList::<T>::insert(&system_token_id, &system_token_metadata);

			Self::set_system_token_status(system_token_id.clone(), system_token_metadata.clone());

			Self::deposit_event(Event::<T>::SystemTokenRegistered {
				system_token_id: system_token_id.clone(),
				system_token_metadata: system_token_metadata.clone(),
			});

			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(1_000)]
		/// Register wrapped system token to other parachain.
		pub fn register_wrapped_system_token(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			wrapped_system_token: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);
			ensure!(
				!SystemTokenOnParachain::<T>::contains_key(&wrapped_system_token),
				Error::<T>::WrappedSystemTokenAlreadyRegistered
			);

			let system_token_metadata = {
				match SystemTokenList::<T>::get(&system_token_id) {
					Some(metadata) => metadata,
					None => Default::default(),
				}
			};

			let config = <configuration::Pallet<T>>::config();
			let xcm = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let root = PalletId(*b"infra/rt");
				let owner: T::AccountId = root.into_account_truncating();

				let mut encoded: Vec<u8> = [wrapped_system_token.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode: Vec<u8> = pallet_assets::Call::<T>::force_create {
					id: wrapped_system_token.clone().asset_id.into(),
					owner: T::Lookup::unlookup(owner.clone()),
					min_balance: <T as pallet_assets::Config>::Balance::from(
						system_token_metadata.clone().min_balance as u128,
					),
					is_sufficient: system_token_metadata.clone().is_sufficient,
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
				<dmp::Pallet<T>>::queue_downward_message(
					&config,
					ParaId::from(wrapped_system_token.clone().para_id).into(),
					xcm,
				) {
				log::error!(
					target: "runtime::system_token_manager",
					"sending 'dmp' failed."
				);
			};

			SystemTokenOnParachain::<T>::insert(&wrapped_system_token, &system_token_id);

			if SystemTokenOnParachainByParaId::<T>::contains_key(
				wrapped_system_token.clone().para_id,
			) {
				let _ = SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
					wrapped_system_token.clone().para_id,
					|maybe_system_tokens| -> Result<(), DispatchError> {
						let system_tokens =
							maybe_system_tokens.as_mut().ok_or(Error::<T>::Unknown)?;
						system_tokens.to_vec().push(wrapped_system_token.clone());
						Ok(())
					},
				);
			} else {
				SystemTokenOnParachainByParaId::<T>::insert(
					&wrapped_system_token.para_id,
					BoundedVec::try_from(vec![wrapped_system_token.clone()]).unwrap(),
				);
			}

			Self::deposit_event(Event::<T>::SystemTokenConverted {
				system_token_id,
				wrapped_system_token: wrapped_system_token.clone(),
			});

			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(1_000)]
		/// Remove the system token.
		pub fn remove_system_token(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);

			let mut system_token_metadata = {
				match SystemTokenList::<T>::get(&system_token_id) {
					Some(metadata) => metadata,
					None => Default::default(),
				}
			};
			system_token_metadata.is_sufficient = false;

			let wrapped_system_tokens = SystemTokenOnParachain::<T>::iter_keys()
				.filter(|wrapped_system_token| {
					SystemTokenOnParachain::<T>::get(wrapped_system_token) ==
						Some(system_token_id.clone())
				})
				.collect::<Vec<SystemTokenId>>();

			for wrapped_system_token in wrapped_system_tokens {
				Self::set_system_token_status(
					wrapped_system_token.clone(),
					system_token_metadata.clone(),
				);
				SystemTokenOnParachain::<T>::remove(&wrapped_system_token);
			}

			Self::set_system_token_status(system_token_id.clone(), system_token_metadata.clone());

			SystemTokenList::<T>::remove(&system_token_id);

			Self::deposit_event(Event::<T>::SystemTokenRemoved {
				system_token_id,
				system_token_metadata,
			});

			Ok(())
		}
	}

	impl<T: Config> Pallet<T>
	where
		u32: PartialEq<<T as pallet_assets::Config>::AssetId>,
		<T as pallet_assets::Config>::Balance: From<u128>,
		<T as pallet_assets::Config>::AssetIdParameter: From<u32>,
	{
		fn set_system_token_status(
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		) {
			let config = <configuration::Pallet<T>>::config();
			let xcm = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let root = PalletId(*b"infra/rt");
				let owner: T::AccountId = root.into_account_truncating();

				let mut encoded: Vec<u8> = [system_token_id.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode: Vec<u8> = pallet_assets::Call::<T>::force_asset_status {
					id: system_token_id.clone().asset_id.into(),
					owner: T::Lookup::unlookup(owner.clone()),
					issuer: T::Lookup::unlookup(owner.clone()),
					admin: T::Lookup::unlookup(owner.clone()),
					freezer: T::Lookup::unlookup(owner.clone()),
					min_balance: <T as pallet_assets::Config>::Balance::from(
						system_token_metadata.clone().min_balance as u128,
					),
					is_sufficient: system_token_metadata.clone().is_sufficient,
					is_frozen: true,
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
				<dmp::Pallet<T>>::queue_downward_message(
					&config,
					ParaId::from(system_token_id.clone().para_id).into(),
					xcm,
				) {
				log::error!(
					target: "runtime::system_token_manager",
					"sending 'dmp' failed."
				);
			};
		}
	}
}

impl<T: Config> SystemTokenInterface for Pallet<T> {
	fn is_system_token(system_token: SystemTokenId) -> bool {
		if let Some(_) = <SystemTokenList<T>>::get(system_token) {
			return true
		}
		false
	}
	fn convert_to_original_system_token(
		wrapped_system_token: WrappedSystemTokenId,
	) -> Option<SystemTokenId> {
		if let Some(s) = <SystemTokenOnParachain<T>>::get(&wrapped_system_token) {
			Self::deposit_event(Event::<T>::SystemTokenConverted {
				wrapped_system_token,
				system_token_id: s.clone(),
			});
			return Some(s)
		}
		None
	}
	fn adjusted_weight(system_token: SystemTokenId, vote_weight: VoteWeight) -> VoteWeight {
		match <SystemTokenList<T>>::get(system_token) {
			Some(meta_data) => {
				let exchange_rate: u128 = meta_data.get_exchange_rate().into();
				return vote_weight.saturating_mul(exchange_rate)
			},
			None => return vote_weight,
		}
	}
}
