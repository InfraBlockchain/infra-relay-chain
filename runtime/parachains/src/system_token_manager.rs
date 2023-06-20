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
	traits::UnixTime,
	PalletId,
};
pub use pallet::*;
use parity_scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AccountIdConversion, ConstU32, StaticLookup},
	types::{SystemTokenId, VoteAssetId, VoteWeight},
	BoundedVec, RuntimeDebug,
};
use sp_std::prelude::*;

pub type ParaAssetId = VoteAssetId;
pub type RelayAssetId = VoteAssetId;
pub type ParaId = u32;
pub type PalletIndex = u32;
pub type SystemTokenWeight = u64;

/// Data structure for Wrapped system tokens
pub type WrappedSystemTokenId = SystemTokenId;

type StringLimit = ConstU32<128>;
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

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct SystemTokenProperty {
	/// weight of this system token
	pub weight: SystemTokenWeight,
	/// epoch time of this system token registered
	pub created_at: u128,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct WrappedSystemTokenProperty {
	/// epoch time of this system token registered
	pub created_at: u128,
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
	use crate::{
		configuration, dmp,
		paras::{self},
	};
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
		/// Time used for computing registration date.
		type UnixTime: UnixTime;
		/// The string limit for name and symbol of system token.
		#[pallet::constant]
		type StringLimit: Get<u32>;
		/// Max number which can be used as system tokens on parachain.
		#[pallet::constant]
		type MaxWrappedSystemToken: Get<u32>;
		/// Max number which can be used as system tokens on parachain.
		#[pallet::constant]
		type MaxSystemTokenOnParachain: Get<u32>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Register a new system token.
		SystemTokenRegistered {
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		},
		/// Deregister the system token.
		SystemTokenDeregistered {
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata,
		},
		/// Register a wrapped system token id to an original system token id.
		WrappedSystemTokenRegistered {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		/// Deregister a wrapped system token id to an original system token id.
		WrappedSystemTokenDeregistered {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		/// Convert a wrapped system token id to an original system token id.
		SystemTokenConverted {
			wrapped_system_token: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		/// Convert a wrapped system token id to an original system token id.
		SetSystemTokenProperty { system_token_id: SystemTokenId, property: SystemTokenProperty },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Failed to register a system token as it is already registered.
		SystemTokenAlreadyRegistered,
		/// Failed to remove the system token as it is not registered.
		SystemTokenNotRegistered,
		SameSystemTokenAlreadyRegistered,
		WrappedSystemTokenAlreadyRegistered,
		WrappedSystemTokenNotRegistered,
		WrongSystemTokenMetadata,
		TooManySystemTokensOnParachain,
		TooManyWrappedSystemTokens,
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
		(SystemTokenMetadata, AssetMetadata),
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn system_token_properties)]
	/// List for original system token and metadata.
	pub(super) type SystemTokenProperties<T: Config> =
		StorageMap<_, Twox64Concat, SystemTokenId, SystemTokenProperty, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn wrapped_system_token_properties)]
	/// List for wrapped system token and metadata.
	pub(super) type WrappedSystemTokenProperties<T: Config> =
		StorageMap<_, Twox64Concat, WrappedSystemTokenId, WrappedSystemTokenProperty, OptionQuery>;

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
	#[pallet::getter(fn para_ids_by_system_token)]
	/// List of parachain ids using system token
	pub(super) type ParaIdsBySystemToken<T: Config> = StorageMap<
		_,
		Twox64Concat,
		SystemTokenId,
		BoundedVec<ParaId, T::MaxSystemTokenOnParachain>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn allowed_system_token)]
	/// Wrapped System token list used in parachains.
	/// Key: (PalletIndex, ParaAssetId) of Wrapped System token. ParaId is omitted.
	/// Value: (SystemTokenId)
	pub(super) type AllowedSystemToken<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		PalletIndex,
		Twox64Concat,
		ParaAssetId,
		SystemTokenId,
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
			weight: SystemTokenWeight,
		) -> DispatchResult {
			ensure_root(origin)?;
			let now_as_millis_u128 = T::UnixTime::now().as_millis();

			ensure!(
				!SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenAlreadyRegistered
			);

			let system_tokens =
				SystemTokenOnParachainByParaId::<T>::get(&system_token_id.clone().para_id)
					.map_or(Default::default(), |system_token| system_token);
			ensure!(
				system_tokens.len() < T::MaxWrappedSystemToken::get() as usize,
				Error::<T>::TooManySystemTokensOnParachain
			);

			Self::set_system_token_status(system_token_id.clone(), true);

			SystemTokenList::<T>::insert(
				&system_token_id,
				(&system_token_metadata, &asset_metadata),
			);
			let property = SystemTokenProperty { weight, created_at: now_as_millis_u128 };
			SystemTokenProperties::<T>::insert(&system_token_id, &property);
			SystemTokenOnParachain::<T>::insert(&system_token_id, &system_token_id);
			Self::insert_system_token_on_parachain_by_para_id(
				system_token_id.clone().para_id,
				system_token_id.clone(),
			);
			Self::insert_para_ids_by_system_token(
				system_token_id.clone(),
				system_token_id.clone().para_id,
			);

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
			let now_as_millis_u128 = T::UnixTime::now().as_millis();

			ensure!(
				SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);
			ensure!(
				!SystemTokenOnParachain::<T>::contains_key(&wrapped_system_token),
				Error::<T>::WrappedSystemTokenAlreadyRegistered
			);

			let para_ids = ParaIdsBySystemToken::<T>::get(&system_token_id)
				.map_or(Default::default(), |para_id| para_id);
			ensure!(
				!para_ids.contains(&wrapped_system_token.clone().para_id),
				Error::<T>::SameSystemTokenAlreadyRegistered
			);
			ensure!(
				para_ids.len() < T::MaxSystemTokenOnParachain::get() as usize,
				Error::<T>::TooManySystemTokensOnParachain
			);

			let system_tokens =
				match SystemTokenOnParachainByParaId::<T>::get(&system_token_id.clone().para_id) {
					Some(system_tokens) => system_tokens,
					None => Default::default(),
				};

			ensure!(
				system_tokens.len() < T::MaxWrappedSystemToken::get() as usize,
				Error::<T>::TooManyWrappedSystemTokens
			);

			Self::create_wrapped_system_token(
				system_token_id.clone(),
				wrapped_system_token.clone(),
			);

			SystemTokenOnParachain::<T>::insert(&wrapped_system_token, &system_token_id);
			let property = WrappedSystemTokenProperty { created_at: now_as_millis_u128 };
			WrappedSystemTokenProperties::<T>::insert(&wrapped_system_token, &property);
			Self::insert_system_token_on_parachain_by_para_id(
				wrapped_system_token.clone().para_id,
				wrapped_system_token.clone(),
			);
			Self::insert_para_ids_by_system_token(
				system_token_id.clone(),
				wrapped_system_token.clone().para_id,
			);
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
						system_tokens.retain(|x| *x != wrapped_system_token.clone());
						Ok(())
					},
				);
			}

			if ParaIdsBySystemToken::<T>::contains_key(system_token_id.clone()) {
				let _ = ParaIdsBySystemToken::<T>::try_mutate_exists(
					system_token_id.clone(),
					|maybe_para_ids| -> Result<(), DispatchError> {
						let para_ids = maybe_para_ids.as_mut().ok_or(Error::<T>::Unknown)?;
						para_ids.retain(|x| *x != wrapped_system_token.clone().para_id.into());
						Ok(())
					},
				);
			}

			WrappedSystemTokenProperties::<T>::remove(&wrapped_system_token);

			Self::deposit_event(Event::<T>::WrappedSystemTokenDeregistered {
				wrapped_system_token,
				system_token_id,
			});

			Ok(())
		}

		#[pallet::call_index(3)]
		#[pallet::weight(1_000)]
		/// Deregister the system token.
		pub fn set_system_token_weight(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			new_weight: SystemTokenWeight,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				SystemTokenProperties::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);

			let mut property = SystemTokenProperties::<T>::get(&system_token_id).unwrap();
			property.weight = new_weight;

			SystemTokenProperties::<T>::insert(&system_token_id, &property);

			Self::deposit_event(Event::<T>::SetSystemTokenProperty { system_token_id, property });

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
					Some((system_token_metadata, _asset_metadata)) => system_token_metadata,
					None => Default::default(),
				}
			};

			let wrapped_system_tokens = SystemTokenOnParachain::<T>::iter_keys()
				.filter(|wrapped_system_token| {
					SystemTokenOnParachain::<T>::get(wrapped_system_token) ==
						Some(system_token_id.clone())
				})
				.collect::<Vec<SystemTokenId>>();

			Self::set_system_token_status(system_token_id.clone(), false);

			for wrapped_system_token in wrapped_system_tokens {
				Self::set_system_token_status(wrapped_system_token.clone(), false);
				SystemTokenOnParachain::<T>::remove(&wrapped_system_token);
				WrappedSystemTokenProperties::<T>::remove(&wrapped_system_token);
				Self::remove_system_token_on_parachain_by_para_id(wrapped_system_token.clone());
			}

			SystemTokenList::<T>::remove(&system_token_id);
			SystemTokenProperties::<T>::remove(&system_token_id);
			SystemTokenOnParachain::<T>::remove(&system_token_id);
			ParaIdsBySystemToken::<T>::remove(&system_token_id);
			Self::remove_system_token_on_parachain_by_para_id(system_token_id.clone());

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
						require_weight_at_most: Weight::from_parts(1_000_000_000, 1_100_000),
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
		fn create_wrapped_system_token(
			system_token_id: SystemTokenId,
			wrapped_system_token: SystemTokenId,
		) {
			let (_system_token_metadata, asset_metadata) = {
				match SystemTokenList::<T>::get(&system_token_id) {
					Some((system_token_metadata, asset_metadata)) =>
						(system_token_metadata, asset_metadata),
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
				let mut call_encode: Vec<u8> =
					pallet_assets::Call::<T>::force_create_with_metadata {
						id: wrapped_system_token.clone().asset_id.into(),
						owner: T::Lookup::unlookup(owner.clone()),
						min_balance: <T as pallet_assets::Config>::Balance::from(
							asset_metadata.min_balance,
						),
						is_sufficient: true,
						name: asset_metadata.clone().name.to_vec(),
						symbol: asset_metadata.clone().symbol.to_vec(),
						decimals: asset_metadata.clone().decimals,
						is_frozen: false,
					}
					.encode();

				create_call_encode.append(&mut call_encode);

				let fee_multilocation =
					MultiAsset { id: Concrete(Here.into()), fun: Fungible(10000) };

				VersionedXcm::from(Xcm(vec![
					BuyExecution {
						fees: fee_multilocation.clone().into(),
						weight_limit: WeightLimit::Unlimited,
					},
					Transact {
						origin_kind: OriginKind::Superuser,
						require_weight_at_most: Weight::from_parts(1_000_000_000, 1_100_000),
						call: create_call_encode.into(),
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
		}
		fn insert_system_token_on_parachain_by_para_id(
			para_id: ParaId,
			system_token_id: SystemTokenId,
		) {
			if SystemTokenOnParachainByParaId::<T>::contains_key(para_id.clone()) {
				let _ = SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
					para_id.clone(),
					|maybe_system_tokens| -> Result<(), DispatchError> {
						let system_tokens =
							maybe_system_tokens.as_mut().ok_or(Error::<T>::Unknown)?;
						system_tokens.try_push(system_token_id.clone()).unwrap_or(());
						Ok(())
					},
				);
			} else {
				SystemTokenOnParachainByParaId::<T>::insert(
					&para_id,
					BoundedVec::try_from(vec![system_token_id.clone()]).unwrap(),
				);
			}
		}
		fn insert_para_ids_by_system_token(system_token_id: SystemTokenId, para_id: ParaId) {
			if ParaIdsBySystemToken::<T>::contains_key(system_token_id.clone()) {
				let _ = ParaIdsBySystemToken::<T>::try_mutate_exists(
					system_token_id.clone(),
					|maybe_para_ids| -> Result<(), DispatchError> {
						let para_ids = maybe_para_ids.as_mut().ok_or(Error::<T>::Unknown)?;
						para_ids.try_push(para_id.clone()).unwrap_or(());
						Ok(())
					},
				);
			} else {
				ParaIdsBySystemToken::<T>::insert(
					&system_token_id,
					BoundedVec::try_from(vec![para_id.clone()]).unwrap(),
				);
			}
		}
		fn remove_system_token_on_parachain_by_para_id(system_token_id: SystemTokenId) {
			if SystemTokenOnParachainByParaId::<T>::contains_key(system_token_id.clone().para_id) &&
				SystemTokenOnParachainByParaId::<T>::get(system_token_id.clone().para_id)
					.unwrap()
					.len() > 1
			{
				let _ = SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
					system_token_id.clone().para_id,
					|maybe_system_tokens| -> Result<(), DispatchError> {
						let system_tokens =
							maybe_system_tokens.as_mut().ok_or(Error::<T>::Unknown)?;
						system_tokens.retain(|x| *x != system_token_id.clone());
						Ok(())
					},
				);
			} else {
				SystemTokenOnParachainByParaId::<T>::remove(&system_token_id.clone().para_id);
			}
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
		match <SystemTokenProperties<T>>::get(system_token) {
			Some(property) => {
				let weight: u128 = property.weight.into();
				return vote_weight.saturating_mul(weight)
			},
			None => return vote_weight,
		}
	}
}
