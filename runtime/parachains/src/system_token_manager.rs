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
pub type PalletIndex = u8;
pub type ExchangeRate = u64;

/// Data structure for Wrapped system tokens
pub type WrappedSystemTokenId = SystemTokenId;

type StringLimit = ConstU32<32>;
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct SystemTokenMetadata {
	/// The user friendly name of issuer in real world
	pub issuer: BoundedVec<u8, StringLimit>,
	/// Description of the token
	pub description: BoundedVec<u8, StringLimit>,
	/// Url of related to the token or issuer
	pub url: BoundedVec<u8, StringLimit>,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct AssetMetadata {
	/// The user friendly name of this system token.
	pub name: BoundedVec<u8, StringLimit>,
	/// The exchange symbol for this system token.
	pub symbol: BoundedVec<u8, StringLimit>,
	/// The number of decimals this asset uses to represent one unit.
	pub decimals: u8,
	/// The minimum balance of this new asset that any single account must
	/// have. If an account's balance is reduced below this, then it collapses to zero.
	pub min_balance: u128,
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
		// Deregister the system token.
		SystemTokenDeregistered {
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		},
		// Register a wrapped system token id to an original system token id.
		WrappedSystemTokenRegistered {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		// Deregister a wrapped system token id to an original system token id.
		WrappedSystemTokenDeregistered {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		// Convert a wrapped system token id to an original system token id.
		SystemTokenConverted {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		// Convert a wrapped system token id to an original system token id.
		SetSystemTokenExchangeRate {
			system_token_id: SystemTokenId,
			exchange_rate: ExchangeRate,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Failed to register a system token as it is already registered.
		SystemTokenAlreadyRegistered,
		/// Failed to remove the system token as it is not registered.
		SystemTokenNotRegistered,
		WrappedSystemTokenAlreadyRegistered,
		WrappedSystemTokenNotRegistered,
		WrongSystemTokenMetadata,
		Unknown,
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	#[pallet::getter(fn system_token_list)]
	/// List for original system token and metadata.
	pub(super) type SystemTokenList<T: Config> = StorageMap<
		_,
		Twox64Concat,
		SystemTokenId,
		(SystemTokenMetadata, AssetMetadata, ExchangeRate),
		OptionQuery,
	>;

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
			asset_metadata: AssetMetadata,
			exchange_rate: ExchangeRate,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				!SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenAlreadyRegistered
			);

			SystemTokenList::<T>::insert(
				&system_token_id,
				(&system_token_metadata, &asset_metadata, &exchange_rate),
			);

			Self::set_system_token_status(system_token_id.clone(), true);

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

			let (system_token_metadata, asset_metadata, exchange_rate) = {
				match SystemTokenList::<T>::get(&system_token_id) {
					Some((system_token_metadata, asset_metadata, exchange_rate)) =>
						(system_token_metadata, asset_metadata, exchange_rate),
					None => Default::default(),
				}
			};

			let config = <configuration::Pallet<T>>::config();
			let xcm = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let root = PalletId(*b"infra/rt");
				let owner: T::AccountId = root.into_account_truncating();

				let mut create_call_encode: Vec<u8> =
					[wrapped_system_token.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode: Vec<u8> = pallet_assets::Call::<T>::force_create {
					id: wrapped_system_token.clone().asset_id.into(),
					owner: T::Lookup::unlookup(owner.clone()),
					min_balance: <T as pallet_assets::Config>::Balance::from(
						asset_metadata.min_balance,
					),
					is_sufficient: true,
				}
				.encode();

				create_call_encode.append(&mut call_encode);

				let mut set_metadata_encoded: Vec<u8> =
					[wrapped_system_token.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode: Vec<u8> = pallet_assets::Call::<T>::force_set_metadata {
					id: wrapped_system_token.clone().asset_id.into(),
					name: asset_metadata.clone().name.to_vec(),
					symbol: asset_metadata.clone().symbol.to_vec(),
					decimals: asset_metadata.clone().decimals,
					is_frozen: false,
				}
				.encode();

				set_metadata_encoded.append(&mut call_encode);

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
						call: create_call_encode.into(),
					},
					Transact {
						origin_kind: OriginKind::Superuser,
						require_weight_at_most: Weight::from_parts(10_000_000_000, 1_100_000),
						call: set_metadata_encoded.into(),
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

			Self::deposit_event(Event::<T>::WrappedSystemTokenRegistered {
				system_token_id,
				wrapped_system_token: wrapped_system_token.clone(),
			});

			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(1_000)]
		/// Deregister wrapped system token to other parachain.
		pub fn deregister_wrapped_system_token(
			origin: OriginFor<T>,
			wrapped_system_token: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				SystemTokenOnParachain::<T>::contains_key(&wrapped_system_token),
				Error::<T>::WrappedSystemTokenNotRegistered
			);

			let system_token_id = SystemTokenOnParachain::<T>::get(&wrapped_system_token).unwrap();

			Self::set_system_token_status(wrapped_system_token.clone(), false);

			SystemTokenOnParachain::<T>::remove(&wrapped_system_token);
			if SystemTokenOnParachainByParaId::<T>::contains_key(
				wrapped_system_token.clone().para_id,
			) {
				let _ = SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
					wrapped_system_token.clone().para_id,
					|maybe_system_tokens| -> Result<(), DispatchError> {
						let system_tokens =
							maybe_system_tokens.as_mut().ok_or(Error::<T>::Unknown)?;
						system_tokens.retain(|&x| x != wrapped_system_token.clone());
						Ok(())
					},
				);
			}

			Self::deposit_event(Event::<T>::WrappedSystemTokenDeregistered {
				wrapped_system_token,
				system_token_id,
			});

			Ok(())
		}

		#[pallet::call_index(3)]
		#[pallet::weight(1_000)]
		/// Deregister the system token.
		pub fn set_system_token_exchange_rate(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			new_exchange_rate: ExchangeRate,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);

			let (system_token_metadata, asset_metadata, exchange_rate) = {
				match SystemTokenList::<T>::get(&system_token_id) {
					Some((system_token_metadata, asset_metadata, exchange_rate)) =>
						(system_token_metadata, asset_metadata, exchange_rate),
					None => Default::default(),
				}
			};

			SystemTokenList::<T>::insert(
				&system_token_id,
				(&system_token_metadata, &asset_metadata, &new_exchange_rate),
			);

			Self::deposit_event(Event::<T>::SetSystemTokenExchangeRate {
				system_token_id,
				exchange_rate: new_exchange_rate,
			});

			Ok(())
		}

		#[pallet::call_index(4)]
		#[pallet::weight(1_000)]
		/// Deregister the system token.
		pub fn deregister_system_token(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);

			let system_token_metadata = {
				match SystemTokenList::<T>::get(&system_token_id) {
					Some((system_token_metadata, asset_metadata, exchange_rate)) =>
						system_token_metadata,
					None => Default::default(),
				}
			};

			let wrapped_system_tokens = SystemTokenOnParachain::<T>::iter_keys()
				.filter(|wrapped_system_token| {
					SystemTokenOnParachain::<T>::get(wrapped_system_token) ==
						Some(system_token_id.clone())
				})
				.collect::<Vec<SystemTokenId>>();

			for wrapped_system_token in wrapped_system_tokens {
				Self::set_system_token_status(wrapped_system_token.clone(), false);
				SystemTokenOnParachain::<T>::remove(&wrapped_system_token);
			}

			Self::set_system_token_status(system_token_id.clone(), false);

			SystemTokenList::<T>::remove(&system_token_id);

			Self::deposit_event(Event::<T>::SystemTokenDeregistered {
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
		fn set_system_token_status(system_token_id: SystemTokenId, is_sufficient: bool) {
			let config = <configuration::Pallet<T>>::config();
			let xcm = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let root = PalletId(*b"infra/rt");
				let owner: T::AccountId = root.into_account_truncating();

				let mut encoded: Vec<u8> = [system_token_id.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode: Vec<u8> = pallet_assets::Call::<T>::set_sufficient {
					id: system_token_id.clone().asset_id.into(),
					is_sufficient,
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
			Some((system_token_metadata, asset_metadata, exchange_rate)) => {
				let exchange_rate: u128 = exchange_rate.into();
				return vote_weight.saturating_mul(exchange_rate)
			},
			None => return vote_weight,
		}
	}
}
