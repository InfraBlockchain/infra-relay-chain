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
use frame_support::{
	pallet_prelude::{OptionQuery, *},
	traits::UnixTime,
	PalletId,
};
pub use pallet::*;
use parity_scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AccountIdConversion, StaticLookup},
	types::{ParaId, SystemTokenId, VoteAssetId, VoteWeight},
	BoundedVec, RuntimeDebug,
};
use sp_std::prelude::*;

pub type ParaAssetId = VoteAssetId;
pub type RelayAssetId = VoteAssetId;
pub type PalletIndex = u32;

pub type SystemTokenWeight = u64;

/// Data structure for Wrapped system tokens
pub type WrappedSystemTokenId = SystemTokenId;
pub type StringLimitOf<T> = <T as Config>::StringLimit;

const REF_WEIGHT: u64 = 500_000_000;
const PROOF_WEIGHT: u64 = 20_000;

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]

pub struct SystemTokenMetadata<BoundedString> {
	/// The user friendly name of issuer in real world
	pub(crate) issuer: BoundedString,
	/// The description of the token
	pub(crate) description: BoundedString,
	/// The url of related to the token or issuer
	pub(crate) url: BoundedString,
	/// The Pallet id of AssetLink in the issued parachain
	pub(crate) asset_link_pallet_id: u8,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct AssetMetadata<BoundedString, Balance> {
	/// The user friendly name of this system token.
	pub(crate) name: BoundedString,
	/// The exchange symbol for this system token.
	pub(crate) symbol: BoundedString,
	/// The number of decimals this asset uses to represent one unit.
	pub(crate) decimals: u8,
	/// The minimum balance of this new asset that any single account must
	/// have. If an account's balance is reduced below this, then it collapses to zero.
	pub(crate) min_balance: Balance,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct SystemTokenProperty {
	/// The weight of this system token
	pub(crate) weight: SystemTokenWeight,
	/// The epoch time of this system token registered
	pub(crate) created_at: u128,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct WrappedSystemTokenProperty {
	/// The pallet id of AseetLink in the parachain which uses the wrapped system token
	/// This could be moved to WrappedSystemTokenMetadata if it needs and exists
	pub(crate) asset_link_pallet_id: u8,
	/// The epoch time of this system token registered
	pub(crate) created_at: u128,
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

pub enum AssetLinkCall {
	/// Register Asset Call on the AssetLink pallet
	LinkAsset,
	/// Deregister Asset Call on the AssetLink pallet
	UnlinkAsset,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use crate::{configuration, dmp, paras};
	use frame_system::pallet_prelude::*;
	use pallet_asset_link::AssetIdOf;

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ configuration::Config
		+ paras::Config
		+ dmp::Config
		+ pallet_assets::Config
		+ pallet_asset_link::Config
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
			system_token_metadata: SystemTokenMetadata<BoundedVec<u8, StringLimitOf<T>>>,
		},
		/// Deregister the system token.
		SystemTokenDeregistered {
			system_token_id: SystemTokenId,
			system_token_metadata: SystemTokenMetadata<BoundedVec<u8, StringLimitOf<T>>>,
		},
		/// Register a wrapped system token id to an original system token id.
		WrappedSystemTokenRegistered {
			wrapped_system_token_id: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		/// Deregister a wrapped system token id to an original system token id.
		WrappedSystemTokenDeregistered {
			wrapped_system_token_id: WrappedSystemTokenId,
			system_token_id: SystemTokenId,
		},
		/// Convert a wrapped system token id to an original system token id.
		SystemTokenConverted {
			wrapped_system_token_id: WrappedSystemTokenId,
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
		/// Key for SystemTokenId is already existed
		SameSystemTokenAlreadyRegistered,
		/// Key for WrappedSystemTokenId, which is for parachain, is already existed
		WrappedSystemTokenAlreadyRegistered,
		/// WrappedSystemToken has not been set for Relay Chain
		WrappedSystemTokenNotRegistered,
		/// Registered System Tokens are out of limit
		TooManySystemTokensOnParachain,
		/// Reigstered WrappedSystemTokens are out of limit
		TooManyWrappedSystemTokens,
		/// Some TryMutate Error
		Unknown,
		/// String metadata is out of limit
		BadMetadata,
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
		(
			SystemTokenMetadata<BoundedVec<u8, StringLimitOf<T>>>,
			AssetMetadata<BoundedVec<u8, StringLimitOf<T>>, T::Balance>,
		),
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
	/// Key: (PalletId, ParaAssetId) of Wrapped System token. ParaId is omitted.
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
		AssetIdOf<T>: From<u32>,
	{
		/// Register a system token.
		#[pallet::call_index(0)]
		#[pallet::weight(1_000)]
		pub fn register_system_token(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			issuer: Vec<u8>,
			description: Vec<u8>,
			url: Vec<u8>,
			origin_asset_link_pallet_id: u8,
			relay_asset_pallet_id: u8,
			relay_wrapped_system_token_asset_id: u32,
			relay_asset_link_pallet_id: u8,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
			min_balance: T::Balance,
			weight: SystemTokenWeight,
		) -> DispatchResult {
			ensure_root(origin.clone())?;

			let original_para_id = system_token_id.clone().para_id;

			// ensure for the validity check
			{
				ensure!(
					!SystemTokenList::<T>::contains_key(&system_token_id),
					Error::<T>::SystemTokenAlreadyRegistered
				);

				let system_tokens = SystemTokenOnParachainByParaId::<T>::get(&original_para_id)
					.map_or(Default::default(), |system_token| system_token);
				ensure!(
					system_tokens.len() < T::MaxWrappedSystemToken::get() as usize,
					Error::<T>::TooManySystemTokensOnParachain
				);
			}

			let (system_token_metadata, asset_metadata) = {
				let s_m = {
					let issuer: BoundedVec<u8, StringLimitOf<T>> =
						issuer.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;
					let description: BoundedVec<u8, StringLimitOf<T>> =
						description.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;
					let url: BoundedVec<u8, StringLimitOf<T>> =
						url.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;

					SystemTokenMetadata {
						issuer,
						description,
						url,
						asset_link_pallet_id: origin_asset_link_pallet_id,
					}
				};

				let a_m = {
					let name: BoundedVec<u8, StringLimitOf<T>> =
						name.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;
					let symbol: BoundedVec<u8, StringLimitOf<T>> =
						symbol.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;

					AssetMetadata { name, symbol, decimals, min_balance }
				};

				(s_m, a_m)
			};

			// Create wrapped token in relay chain
			let relay_wrapped_system_token_id = SystemTokenId {
				para_id: 0,
				pallet_id: relay_asset_pallet_id,
				asset_id: relay_wrapped_system_token_asset_id,
			};

			let root = PalletId(*b"infra/rt");
			let owner: T::AccountId = root.into_account_truncating();

			let _ = pallet_assets::pallet::Pallet::<T>::force_create_with_metadata(
				origin.clone(),
				relay_wrapped_system_token_asset_id.into(),
				T::Lookup::unlookup(owner.clone()),
				true,
				min_balance,
				name,
				symbol,
				decimals,
				false,
				system_token_id,
			);

			// Storage insert logics
			{
				let now_as_millis_u128 = T::UnixTime::now().as_millis();
				let property = SystemTokenProperty { weight, created_at: now_as_millis_u128 };

				SystemTokenProperties::<T>::insert(&system_token_id, &property);

				SystemTokenOnParachain::<T>::insert(&system_token_id, &system_token_id);
				SystemTokenOnParachain::<T>::insert(
					&relay_wrapped_system_token_id,
					&system_token_id,
				);

				SystemTokenList::<T>::insert(
					&system_token_id,
					(&system_token_metadata, &asset_metadata),
				);

				Self::insert_system_token_on_parachain_by_para_id(
					original_para_id,
					system_token_id.clone(),
				);
				Self::insert_para_ids_by_system_token(system_token_id.clone(), original_para_id);

				// relay chain wrapped system token state
				let wrapped_system_token_property = WrappedSystemTokenProperty {
					asset_link_pallet_id: relay_asset_link_pallet_id,
					created_at: now_as_millis_u128,
				};

				Self::insert_system_token_on_parachain_by_para_id(
					relay_wrapped_system_token_id.clone().para_id,
					relay_wrapped_system_token_id.clone(),
				);
				Self::insert_para_ids_by_system_token(
					system_token_id.clone(),
					relay_wrapped_system_token_id.clone().para_id,
				);
				WrappedSystemTokenProperties::<T>::insert(
					&relay_wrapped_system_token_id,
					&wrapped_system_token_property,
				);
			}

			// DMP call to the parachain
			Self::set_system_token_status(system_token_id.clone(), true);

			Self::deposit_event(Event::<T>::SystemTokenRegistered {
				system_token_id,
				system_token_metadata,
			});

			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(1_000)]
		/// Register the wrapped system token to other parachain.
		pub fn register_wrapped_system_token(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			wrapped_system_token_id: WrappedSystemTokenId,
			wrapped_asset_link_pallet_id: u8,
		) -> DispatchResult {
			ensure_root(origin.clone())?;

			let original_para_id = system_token_id.clone().para_id;
			let wrapped_para_id = wrapped_system_token_id.clone().para_id;

			// ensure for the validity check
			{
				ensure!(
					SystemTokenList::<T>::contains_key(&system_token_id),
					Error::<T>::SystemTokenNotRegistered
				);
				ensure!(
					!SystemTokenOnParachain::<T>::contains_key(&wrapped_system_token_id),
					Error::<T>::WrappedSystemTokenAlreadyRegistered
				);

				let para_ids = ParaIdsBySystemToken::<T>::get(&system_token_id)
					.map_or(Default::default(), |para_id| para_id);

				ensure!(
					!para_ids.contains(&wrapped_para_id),
					Error::<T>::SameSystemTokenAlreadyRegistered
				);
				ensure!(
					para_ids.len() < T::MaxSystemTokenOnParachain::get() as usize,
					Error::<T>::TooManySystemTokensOnParachain
				);

				let system_tokens =
					match SystemTokenOnParachainByParaId::<T>::get(&original_para_id) {
						Some(system_tokens) => system_tokens,
						None => Default::default(),
					};
				ensure!(
					system_tokens.len() < T::MaxWrappedSystemToken::get() as usize,
					Error::<T>::TooManyWrappedSystemTokens
				);
			}

			SystemTokenOnParachain::<T>::insert(&wrapped_system_token_id, &system_token_id);
			{
				let now_as_millis_u128 = T::UnixTime::now().as_millis();
				let property = WrappedSystemTokenProperty {
					asset_link_pallet_id: wrapped_asset_link_pallet_id,
					created_at: now_as_millis_u128,
				};
				WrappedSystemTokenProperties::<T>::insert(&wrapped_system_token_id, &property);
			}

			Self::insert_system_token_on_parachain_by_para_id(
				wrapped_para_id,
				wrapped_system_token_id.clone(),
			);
			Self::insert_para_ids_by_system_token(system_token_id.clone(), wrapped_para_id);

			// Register wrapped system token in relay chain
			if wrapped_system_token_id.clone().para_id == 0.into() {
				let (_, asset_metadata) = SystemTokenList::<T>::get(&system_token_id)
					.ok_or("metadata should be obtained")?;

				let root = PalletId(*b"infra/rt");
				let owner: T::AccountId = root.into_account_truncating();

				let _ = pallet_assets::pallet::Pallet::<T>::force_create_with_metadata(
					origin.clone(),
					wrapped_system_token_id.clone().asset_id.into(),
					T::Lookup::unlookup(owner.clone()),
					true,
					asset_metadata.min_balance,
					asset_metadata.clone().name.to_vec(),
					asset_metadata.clone().symbol.to_vec(),
					asset_metadata.clone().decimals,
					false,
					system_token_id,
				);
			} else {
				Self::create_wrapped_system_token(
					system_token_id.clone(),
					wrapped_system_token_id.clone(),
				)?;
			}

			Self::deposit_event(Event::<T>::WrappedSystemTokenRegistered {
				system_token_id,
				wrapped_system_token_id,
			});

			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(1_000)]
		/// Deregister wrapped system token to other parachain.
		pub fn deregister_wrapped_system_token(
			origin: OriginFor<T>,
			wrapped_system_token_id: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin.clone())?;
			ensure!(
				SystemTokenOnParachain::<T>::contains_key(&wrapped_system_token_id),
				Error::<T>::WrappedSystemTokenNotRegistered
			);

			let system_token_id = SystemTokenOnParachain::<T>::get(&wrapped_system_token_id)
				.ok_or("original system token id should be obtained")?;

			SystemTokenOnParachain::<T>::remove(&wrapped_system_token_id);
			if SystemTokenOnParachainByParaId::<T>::contains_key(
				wrapped_system_token_id.clone().para_id,
			) {
				let _ = SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
					wrapped_system_token_id.clone().para_id,
					|maybe_system_tokens| -> Result<(), DispatchError> {
						let system_tokens =
							maybe_system_tokens.as_mut().ok_or(Error::<T>::Unknown)?;
						system_tokens.retain(|x| *x != wrapped_system_token_id.clone());
						Ok(())
					},
				);
			}

			if ParaIdsBySystemToken::<T>::contains_key(system_token_id.clone()) {
				let _ = ParaIdsBySystemToken::<T>::try_mutate_exists(
					system_token_id.clone(),
					|maybe_para_ids| -> Result<(), DispatchError> {
						let para_ids = maybe_para_ids.as_mut().ok_or(Error::<T>::Unknown)?;
						para_ids.retain(|x| *x != wrapped_system_token_id.clone().para_id.into());
						Ok(())
					},
				);
			}

			let original_asset_link_pallet_id = {
				let (system_token_metadata, _asset_metadata) =
					SystemTokenList::<T>::get(&system_token_id)
						.ok_or("metadata should be obtained")?;
				system_token_metadata.asset_link_pallet_id
			};

			WrappedSystemTokenProperties::<T>::remove(&wrapped_system_token_id);

			// Deregister wrapped system token in relay chain
			if wrapped_system_token_id.clone().para_id == 0.into() {
				let _ = pallet_assets::pallet::Pallet::<T>::set_sufficient_with_unlink_system_token(
					origin.clone(),
					wrapped_system_token_id.clone().asset_id.into(),
					false,
				);
			} else {
				// DMP calls
				Self::set_system_token_status(wrapped_system_token_id.clone(), false);
				Self::unlink_asset(system_token_id, original_asset_link_pallet_id)?;
			}

			Self::deposit_event(Event::<T>::WrappedSystemTokenDeregistered {
				wrapped_system_token_id,
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

			let mut property = SystemTokenProperties::<T>::get(&system_token_id)
				.ok_or("property should be obtained")?;
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
			ensure_root(origin.clone())?;

			ensure!(
				SystemTokenList::<T>::contains_key(&system_token_id),
				Error::<T>::SystemTokenNotRegistered
			);

			let (system_token_metadata, _asset_metadata) =
				SystemTokenList::<T>::get(&system_token_id).ok_or("metadata should be obtained")?;

			{
				let wrapped_system_tokens = SystemTokenOnParachain::<T>::iter_keys()
					.filter(|wrapped_system_token_id| {
						SystemTokenOnParachain::<T>::get(wrapped_system_token_id) ==
							Some(system_token_id.clone())
					})
					.collect::<Vec<SystemTokenId>>();

				for wrapped_system_token_id in wrapped_system_tokens {
					if wrapped_system_token_id.para_id == 0.into() {
						let _ = pallet_assets::pallet::Pallet::<T>::set_sufficient_with_unlink_system_token(
							origin.clone(),
							wrapped_system_token_id.asset_id.into(),
							false,
						);
					} else {
						Self::set_system_token_status(wrapped_system_token_id.clone(), false);
					}
					SystemTokenOnParachain::<T>::remove(&wrapped_system_token_id);
					WrappedSystemTokenProperties::<T>::remove(&wrapped_system_token_id);
					Self::remove_system_token_on_parachain_by_para_id(
						wrapped_system_token_id.clone(),
					);
				}
			}

			SystemTokenList::<T>::remove(&system_token_id);
			SystemTokenProperties::<T>::remove(&system_token_id);
			SystemTokenOnParachain::<T>::remove(&system_token_id);
			ParaIdsBySystemToken::<T>::remove(&system_token_id);
			Self::remove_system_token_on_parachain_by_para_id(system_token_id.clone());

			Self::set_system_token_status(system_token_id.clone(), false);

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
		AssetIdOf<T>: From<u32>,
	{
		fn set_system_token_status(system_token_id: SystemTokenId, is_sufficient: bool) {
			let config = <configuration::Pallet<T>>::config();
			let xcm = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let mut encoded: Vec<u8> = [system_token_id.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode = match is_sufficient {
					true => pallet_assets::Call::<T>::set_sufficient {
						id: system_token_id.clone().asset_id.into(),
						is_sufficient,
					}
					.encode(),
					false => pallet_assets::Call::<T>::set_sufficient_with_unlink_system_token {
						id: system_token_id.clone().asset_id.into(),
						is_sufficient,
					}
					.encode(),
				};

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
						require_weight_at_most: Weight::from_parts(REF_WEIGHT, PROOF_WEIGHT),
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
			wrapped_system_token_id: WrappedSystemTokenId,
		) -> DispatchResult {
			let (system_token_metadata, asset_metadata) =
				SystemTokenList::<T>::get(&system_token_id).ok_or("metadata should be obtained")?;
			let original_asset_link_pallet_id = system_token_metadata.asset_link_pallet_id;

			let config = <configuration::Pallet<T>>::config();

			let xcm = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let root = PalletId(*b"infra/rt");
				let owner: T::AccountId = root.into_account_truncating();

				let mut create_call_encode: Vec<u8> =
					[wrapped_system_token_id.clone().pallet_id as u8].into(); // asset pallet number
				let mut call_encode: Vec<u8> =
					pallet_assets::Call::<T>::force_create_with_metadata {
						id: wrapped_system_token_id.clone().asset_id.into(),
						owner: T::Lookup::unlookup(owner.clone()),
						min_balance: asset_metadata.min_balance,
						is_sufficient: true,
						name: asset_metadata.clone().name.to_vec(),
						symbol: asset_metadata.clone().symbol.to_vec(),
						decimals: asset_metadata.clone().decimals,
						is_frozen: false,
						system_token_id,
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
						// require_weight_at_most: Weight::from_parts(1_000_000_000, 1_100_000),
						require_weight_at_most: Weight::from_parts(REF_WEIGHT, PROOF_WEIGHT),
						call: create_call_encode.into(),
					},
				]))
				.encode()
			};

			if let Err(dmp::QueueDownwardMessageError::ExceedsMaxMessageSize) =
				<dmp::Pallet<T>>::queue_downward_message(
					&config,
					ParaId::from(wrapped_system_token_id.clone().para_id).into(),
					xcm,
				) {
				log::error!(
					target: "runtime::system_token_manager",
					"sending 'create_asset dmp's failed."
				);
			};

			let asset_link_call = AssetLinkCall::LinkAsset;

			// para which issued original STI
			Self::call_dmp_asset_link(
				&asset_link_call,
				original_asset_link_pallet_id,
				system_token_id,
				wrapped_system_token_id,
			);

			Ok(())
		}

		fn unlink_asset(
			system_token_id: SystemTokenId,
			wrapped_asset_link_pallet_id: u8,
		) -> DispatchResult {
			let asset_link_call = AssetLinkCall::UnlinkAsset;
			let dummy_system_token_id = SystemTokenId::default();
			Self::call_dmp_asset_link(
				&asset_link_call,
				wrapped_asset_link_pallet_id,
				system_token_id,
				dummy_system_token_id,
			);

			Ok(())
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

		fn call_dmp_asset_link(
			asset_link_call: &AssetLinkCall,
			asset_link_pallet_id: u8,
			local_system_token_id: SystemTokenId,
			target_system_token_id: SystemTokenId,
		) {
			let config = <configuration::Pallet<T>>::config();

			let xcm_asset_link = {
				use parity_scale_codec::Encode as _;
				use xcm::opaque::{latest::prelude::*, VersionedXcm};

				let mut create_call_encode: Vec<u8> = [asset_link_pallet_id as u8].into();

				let mut call_encode: Vec<u8> = match asset_link_call {
					AssetLinkCall::LinkAsset => pallet_asset_link::Call::<T>::link_system_token {
						asset_id: local_system_token_id.asset_id.into(),
						system_token_id: target_system_token_id,
					}
					.encode(),
					AssetLinkCall::UnlinkAsset =>
						pallet_asset_link::Call::<T>::unlink_system_token {
							asset_id: local_system_token_id.asset_id.into(),
						}
						.encode(),
				};

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
						// require_weight_at_most: Weight::from_parts(1_000_000_000, 1_100_000),
						require_weight_at_most: Weight::from_parts(REF_WEIGHT, PROOF_WEIGHT),
						call: create_call_encode.into(),
					},
				]))
				.encode()
			};

			if let Err(dmp::QueueDownwardMessageError::ExceedsMaxMessageSize) =
				<dmp::Pallet<T>>::queue_downward_message(
					&config,
					ParaId::from(local_system_token_id.clone().para_id).into(),
					xcm_asset_link,
				) {
				log::error!(
					target: "runtime::system_token_manager",
					"sending 'register_asset dmp' failed."
				);
			};
		}
	}
}

impl<T: Config> SystemTokenInterface for Pallet<T> {
	fn is_system_token(system_token_id: SystemTokenId) -> bool {
		if let Some(_) = <SystemTokenList<T>>::get(system_token_id) {
			return true
		}
		false
	}
	fn convert_to_original_system_token(
		wrapped_system_token_id: WrappedSystemTokenId,
	) -> Option<SystemTokenId> {
		if let Some(s) = <SystemTokenOnParachain<T>>::get(&wrapped_system_token_id) {
			Self::deposit_event(Event::<T>::SystemTokenConverted {
				wrapped_system_token_id,
				system_token_id: s.clone(),
			});
			return Some(s)
		}
		None
	}
	fn adjusted_weight(system_token_id: SystemTokenId, vote_weight: VoteWeight) -> VoteWeight {
		match <SystemTokenProperties<T>>::get(system_token_id) {
			Some(property) => {
				let weight: u128 = property.weight.into();
				return vote_weight.saturating_mul(weight)
			},
			None => return vote_weight,
		}
	}
}
