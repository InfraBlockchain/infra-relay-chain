// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{configuration, dmp, paras};
pub use frame_support::{
	pallet_prelude::*,
	traits::{ibs_support::system_token::SystemTokenInterface, UnixTime},
	PalletId,
};
use frame_system::pallet_prelude::*;
use pallet_asset_link::AssetIdOf;

pub use pallet::*;
use parity_scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AccountIdConversion, StaticLookup},
	types::{
		AssetId as IbsAssetId, PalletId as IbsPalletId, ParaId as IbsParaId, SystemTokenId,
		SystemTokenWeight, VoteWeight,
	},
	BoundedVec, RuntimeDebug,
};
use sp_std::prelude::*;

pub type StringLimitOf<T> = <T as Config>::StringLimit;
pub type IbsMetadata<T> = (
	SystemTokenMetadata<BoundedVec<u8, StringLimitOf<T>>>,
	AssetMetadata<BoundedVec<u8, StringLimitOf<T>>, <T as pallet_assets::Config>::Balance>,
);

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo)]
pub enum SystemTokenType {
	Original(SystemTokenId),
	Wrapped(SystemTokenId),
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo)]
pub struct ParaCallMetadata {
	para_id: IbsParaId,
	pallet_id: IbsPalletId,
	pallet_name: Vec<u8>,
	call_name: Vec<u8>,
}

/// The base_system_token_weight. Assume that it SHOULD not be changed.
const BASE_SYSTEM_TOKEN_WEIGHT: u128 = 100_000;

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]

/// Metadata of the `original` system token for Relay Chain
pub struct SystemTokenMetadata<BoundedString> {
	/// The user friendly name of issuer in real world
	pub(crate) issuer: BoundedString,
	/// The description of the token
	pub(crate) description: BoundedString,
	/// The url of related to the token or issuer
	pub(crate) url: BoundedString,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
/// Metadata of the `original` local asset based on parachain
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
	// The weight of this system token. Only 'original` system token would have its weight
	pub(crate) system_token_weight: Option<SystemTokenWeight>,
	// The epoch time of this system token registered
	pub(crate) created_at: u128,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ configuration::Config
		+ paras::Config
		+ dmp::Config
		+ pallet_assets::Config
		+ pallet_asset_link::Config
		+ pallet_system_token::Config
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
		SystemTokenRegistered { original: SystemTokenId },
		/// Deregister the system token.
		SystemTokenDeregistered { original: SystemTokenId },
		/// Register a wrapped system token id to an original system token id.
		WrappedSystemTokenRegistered { original: SystemTokenId, wrapped: SystemTokenId },
		/// Deregister a wrapped system token id to an original system token id.
		WrappedSystemTokenDeregistered { wrapped: SystemTokenId },
		/// Convert a wrapped system token id to an original system token id.
		SystemTokenConverted { wrapped: SystemTokenId, original: SystemTokenId },
		/// Update the weight for system token. The weight is calculated with exchange_rate and decimal.
		SetSystemTokenWeight { original: SystemTokenId, property: SystemTokenProperty },
		/// Update the fee rate of the parachain. The default value is 1_000(1).
		SetParaFeeRate { para_id: IbsParaId, para_fee_rate: u32 },
		/// Update the fee rate of the parachain. The default value is 1_000(1).
		SetFeeTable { para_call_metadata: ParaCallMetadata, fee: T::Balance },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Requested system token is already registered.
		SystemTokenAlreadyRegistered,
		/// Failed to remove the system token as it is not registered.
		SystemTokenNotRegistered,
		/// Requested sytem token has already registered
		WrappedAlreadyRegistered,
		/// WrappedSystemToken has not been set for Relay Chain
		WrappedNotRegistered,
		/// Registered System Tokens are out of limit
		TooManySystemTokensOnParachain,
		/// Reigstered WrappedSystemTokens are out of limit
		TooManyWrapped,
		/// Some TryMutate Error
		Unknown,
		/// String metadata is out of limit
		BadMetadata,
		/// Some of the value are not exist
		NotFound,
		/// Error occurred on sending XCM
		DmpError,
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	#[pallet::getter(fn system_token_list)]
	/// Metadata(`SystemTokenMetadata`, `AssetMetadata`) of `original` system token
	pub(super) type OrigingalSystemTokenMetadata<T: Config> =
		StorageMap<_, Blake2_128Concat, SystemTokenId, IbsMetadata<T>, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn system_token_properties)]
	/// List for original system token and metadata.
	pub(super) type SystemTokenProperties<T: Config> =
		StorageMap<_, Blake2_128Concat, SystemTokenId, SystemTokenProperty, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn system_token_on_parachain)]
	/// Stored when `wrapped` system token is registered
	/// 
	/// Key
	/// 
	/// - `wrapped` system token id
	/// 
	/// Value
	/// 
	/// - `original` system token id
	/// 
	/// Used for converting `wrapped` system token to `original` system token
	pub(super) type SystemTokenOnParachain<T: Config> =
		StorageMap<_, Blake2_128Concat, SystemTokenId, SystemTokenId, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn system_token_on_parachain_by_para_id)]
	/// System token list for specific parachain by ParaId.
	pub(super) type SystemTokenOnParachainByParaId<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		IbsParaId,
		BoundedVec<SystemTokenId, T::MaxWrappedSystemToken>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn para_ids_by_system_token)]
	/// List of parachain ids using system token
	pub(super) type ParaIdsBySystemToken<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		SystemTokenId,
		BoundedVec<IbsParaId, T::MaxSystemTokenOnParachain>,
		OptionQuery,
	>;

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		<T as pallet_assets::Config>::AssetIdParameter: From<IbsAssetId>,
		AssetIdOf<T>: From<IbsAssetId>,
	{
		// Description:
		// Register system token after creating local asset on original chain.
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - system_token_id: Original system token id expected to be registered
		// - issuer: Human-readable issuer of system token which is metadata for Relay Chain
		// - description: Human-readable description of system token which is metadata for Relay Chain
		// - url: Human-readable url of system token which is metadata for Relay Chain
		// - name: Name of system token which is same as original chain
		// - symbol: Symbol of system token which is same as original chain
		// - decimals: Decimal of system token which is same as original chain
		// - min_balance: Min balance of system token to be alive which is same as original chain
		// - system_token_weight: Weight of system token which is same as original chain
		//
		// Logic:
		// Once it is accepted by governance,
		// `try_register_original` and `try_set_sufficient_and_weight` will be called,
		// which will change `original` system token state
		#[pallet::call_index(0)]
		#[pallet::weight(1_000)]
		pub fn register_system_token(
			origin: OriginFor<T>,
			original: SystemTokenId,
			system_token_weight: SystemTokenWeight,
			issuer: Vec<u8>,
			description: Vec<u8>,
			url: Vec<u8>,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
			min_balance: T::Balance,
		) -> DispatchResult {
			ensure_root(origin.clone())?;
			Self::try_register_original(
				&original,
				system_token_weight,
				&issuer,
				&description,
				&url,
				&name,
				&symbol,
				decimals,
				min_balance,
			)?;

			Self::try_set_sufficient_and_weight(&original, true, Some(system_token_weight))?;

			Self::deposit_event(Event::<T>::SystemTokenRegistered { original });

			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(1_000)]
		// Description
		// Register wrapped system token which has wrapped the original system token
		// One parachain will request its needs to use system token as their utility token(e.g transaction fee).
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - original: Original system token id expected to be registered
		// - wrapped: System token id which wrapped the original system token
		//
		// Logic:
		// Once it is accepted by governance,
		// - 'try_register_wsys_token': Try register wrapped_system_token and return weight of system token
		// - 'try_create_wrapped': Send DMP to create local asset based on `wrapped_system_token_id`
		pub fn register_wrapped_system_token(
			origin: OriginFor<T>,
			original: SystemTokenId,
			wrapped: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin.clone())?;

			let system_token_weight = Self::try_register_wrapped(&original, &wrapped)?;

			Self::try_create_wrapped(origin.clone(), wrapped, system_token_weight)?;

			Self::deposit_event(Event::<T>::WrappedSystemTokenRegistered { original, wrapped });

			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(1_000)]
		// Description:
		// Deregister all `original` and `wrapped` system token registered on runtime.
		// Deregistered system token is no longer used as `transaction fee`
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - system_token_id: Original system token id expected to be deregistered
		pub fn deregister_system_token(
			origin: OriginFor<T>,
			original: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin.clone())?;
			Self::try_deregister_all(&origin, original)?;
			Self::deposit_event(Event::<T>::SystemTokenDeregistered { original });

			Ok(())
		}

		#[pallet::call_index(3)]
		#[pallet::weight(1_000)]
		// Description:
		// Deregister a wrapped system token, which has been used to other parachain.
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - wsys_token_id: Wrapped system token id expected to be deregistered
		//
		// Logic:
		// DMP
		// - Set`sufficient` to `false`
		// - 'unlink' the system token with local asset
		pub fn deregister_wrapped_system_token(
			origin: OriginFor<T>,
			wrapped: SystemTokenId,
		) -> DispatchResult {
			ensure_root(origin.clone())?;
			Self::try_deregister(SystemTokenType::Wrapped(wrapped))?;
			Self::try_set_sufficient_and_unlink(&origin, wrapped.clone(), false)?;

			Self::deposit_event(Event::<T>::WrappedSystemTokenDeregistered { wrapped });

			Ok(())
		}

		#[pallet::call_index(4)]
		#[pallet::weight(1_000)]
		// Description:
		// Update the weight of system token, which can affect on PoT vote
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - system_token_id: System token id expected to be updated
		// - system_token_weight: System token weight expected to be updated
		pub fn update_system_token_weight(
			origin: OriginFor<T>,
			original: SystemTokenId,
			system_token_weight: SystemTokenWeight,
		) -> DispatchResult {
			ensure_root(origin.clone())?;

			let wsys_tokens = Self::try_get_wsys_token_list(&original)?;
			for wsys_token_id in wsys_tokens.iter() {
				Self::try_update_weight_of_wrapped(
					origin.clone(),
					wsys_token_id,
					system_token_weight,
				)?;
			}
			Self::try_update_weight_property_of_original(original, system_token_weight)?;

			Ok(())
		}

		#[pallet::call_index(5)]
		#[pallet::weight(1_000)]
		// Description:
		// Try send DMP for encoded `update_para_fee_rate` to given `para_id`
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - para_id: Destination of DMP
		// - pallet_id: Pallet index of `update_fee_para_rate`
		// - para_fee_rate: Fee rate for specific parachain expected to be updated
		pub fn update_fee_para_rate(
			origin: OriginFor<T>,
			para_id: IbsParaId,
			pallet_id: IbsPalletId,
			para_fee_rate: u32,
		) -> DispatchResult {
			ensure_root(origin)?;

			let encoded_call: Vec<u8> =
				pallet_assets::Call::<T>::update_para_fee_rate { para_fee_rate }.encode();
			system_token_xcm_handler::try_queue_dmp::<T>(para_id, pallet_id, encoded_call)?;
			Self::deposit_event(Event::<T>::SetParaFeeRate { para_id, para_fee_rate });

			Ok(())
		}

		#[pallet::call_index(6)]
		#[pallet::weight(1_000)]
		// Description:
		// Setting fee for parachain-specific calls(extrinsics).
		//
		// Origin:
		// ** Root(Authorized) privileged call **
		//
		// Params:
		// - para_id: Id of the parachain of which fee to be set
		// - pallet_id: Pallet index of `System Token`
		// - pallet_name: Name of the pallet of which extrinsic is defined
		// - call_name: Name of the call(extrinsic) of which fee to be set
		// - fee: Amount of fee to be set
		//
		// Logic:
		// When fee is charged on the parachain, extract the metadata of the call, which is 'pallet_name' and 'call_name'
		// Lookup the fee table with `key = (pallet_name, call_name)`.
		// If value exists, we charged with that fee. Otherwise, default fee will be charged
		pub fn set_fee_table(
			origin: OriginFor<T>,
			para_call_metadata: ParaCallMetadata,
			fee: T::Balance,
		) -> DispatchResult {
			ensure_root(origin)?;

			let ParaCallMetadata { para_id, pallet_id, pallet_name, call_name } =
				para_call_metadata.clone();
			let encoded_call: Vec<u8> =
				pallet_system_token::Call::<T>::set_fee_table { pallet_name, call_name, fee }
					.encode();
			system_token_xcm_handler::try_queue_dmp::<T>(para_id, pallet_id, encoded_call)?;

			Self::deposit_event(Event::<T>::SetFeeTable { para_call_metadata, fee });

			Ok(())
		}
	}
}

// System token related interal methods
impl<T: Config> Pallet<T>
where
	<T as pallet_assets::Config>::AssetIdParameter: From<IbsAssetId>,
	AssetIdOf<T>: From<IbsAssetId>,
{
	fn unix_time() -> u128 {
		T::UnixTime::now().as_millis()
	}

	fn system_token_metadata(
		issuer: &Vec<u8>,
		description: &Vec<u8>,
		url: &Vec<u8>,
	) -> Result<SystemTokenMetadata<BoundedVec<u8, StringLimitOf<T>>>, DispatchError> {
		let issuer = issuer.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;
		let description = description.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;
		let url = url.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;

		Ok(SystemTokenMetadata { issuer, description, url })
	}

	fn asset_metadata(
		name: &Vec<u8>,
		symbol: &Vec<u8>,
		decimals: u8,
		min_balance: T::Balance,
	) -> Result<AssetMetadata<BoundedVec<u8, StringLimitOf<T>>, T::Balance>, DispatchError> {
		let name = name.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;
		let symbol = symbol.clone().try_into().map_err(|_| Error::<T>::BadMetadata)?;

		Ok(AssetMetadata { name, symbol, decimals, min_balance })
	}

	/// Try get list of `wrapped` system tokens which is mapped to `original`
	///
	/// Validity
	///
	/// - Ensure `original` system token is already registered
	fn try_get_wsys_token_list(original: &SystemTokenId) -> Result<Vec<SystemTokenId>, Error<T>> {
		ensure!(
			SystemTokenProperties::<T>::contains_key(&original),
			Error::<T>::SystemTokenNotRegistered
		);
		let token_list = SystemTokenOnParachain::<T>::iter_keys()
			.filter(|wrapped| {
				SystemTokenOnParachain::<T>::get(wrapped).as_ref() == Some(original)
			})
			.collect::<Vec<SystemTokenId>>();
		Ok(token_list)
	}

	/// Try register `original` system token on runtime.
	///
	/// Validity
	///
	/// - Ensure `original` system token is not registered in `OrigingalSystemTokenMetadata`
	///
	/// State changes
	///
	/// `SystemTokenOnParachainByParaId`, `ParaIdsBySystemToken`, `SystemTokenProperties`, `SystemTokenOnParachain`, `OrigingalSystemTokenMetadata`
	fn try_register_original(
		original: &SystemTokenId,
		system_token_weight: SystemTokenWeight,
		issuer: &Vec<u8>,
		description: &Vec<u8>,
		url: &Vec<u8>,
		name: &Vec<u8>,
		symbol: &Vec<u8>,
		decimals: u8,
		min_balance: T::Balance,
	) -> DispatchResult {
		ensure!(
			!OrigingalSystemTokenMetadata::<T>::contains_key(&original),
			Error::<T>::SystemTokenAlreadyRegistered
		);
		let system_token_metadata = Self::system_token_metadata(&issuer, &description, &url)?;
		let asset_metadata = Self::asset_metadata(&name, &symbol, decimals, min_balance)?;
		let SystemTokenId { para_id, .. } = original.clone();
		Self::try_push_original_for_para_id(para_id, &original)?;
		Self::try_push_para_id(para_id, &original)?;

		SystemTokenProperties::<T>::insert(
			&original,
			SystemTokenProperty {
				system_token_weight: Some(system_token_weight),
				created_at: Self::unix_time(),
			},
		);
		// Self registered as wrapped token, which would be used for knowing it is 'original system token'
		SystemTokenOnParachain::<T>::insert(&original, &original);

		OrigingalSystemTokenMetadata::<T>::insert(
			&original,
			(&system_token_metadata, &asset_metadata),
		);

		Ok(())
	}

	/// Try register `wrapped_system_token` and return `weight` of system token
	///
	/// Validity
	///
	/// - `SystemTokenId` is already registered.
	///
	/// - `WrappedSystemTokenId` is not registered yet.
	///
	/// - `ParaId` is not registered yet.
	///
	/// State changes
	///
	/// - `SystemTokenOnParachain`, `SystemTokenOnParachainByParaId`, `ParaIdsBySystemToken`
	fn try_register_wrapped(
		original: &SystemTokenId,
		wrapped: &SystemTokenId,
	) -> Result<SystemTokenWeight, DispatchError> {
		ensure!(
			OrigingalSystemTokenMetadata::<T>::contains_key(original),
			Error::<T>::SystemTokenNotRegistered
		);
		ensure!(
			!SystemTokenOnParachain::<T>::contains_key(wrapped),
			Error::<T>::WrappedAlreadyRegistered
		);

		let SystemTokenId { para_id, .. } = wrapped.clone();

		let para_ids =
			ParaIdsBySystemToken::<T>::get(original).map_or(Default::default(), |para_id| para_id);
		ensure!(!para_ids.contains(&para_id), Error::<T>::SystemTokenAlreadyRegistered);

		SystemTokenOnParachain::<T>::insert(wrapped, original);
		SystemTokenProperties::<T>::insert(
			wrapped,
			&SystemTokenProperty { system_token_weight: None, created_at: Self::unix_time() },
		);

		Self::try_push_original_for_para_id(para_id, wrapped)?;
		Self::try_push_para_id(para_id, original)?;

		let property = SystemTokenProperties::<T>::get(original).ok_or(Error::<T>::NotFound)?;
		let weight = property.system_token_weight.map_or(BASE_SYSTEM_TOKEN_WEIGHT, |w| w);
		Ok(weight)
	}

	/// Try deregister for all `original` and `wrapped` system tokens
	fn try_deregister_all(origin: &OriginFor<T>, original: SystemTokenId) -> DispatchResult {
		// Wrapped related
		let wsys_tokens = Self::try_get_wsys_token_list(&original)?;
		for wsys_token_id in wsys_tokens {
			Self::try_set_sufficient_and_unlink(origin, wsys_token_id, false)?;
			Self::try_deregister(SystemTokenType::Wrapped(wsys_token_id))?;
		}

		// Original related
		Self::try_deregister(SystemTokenType::Original(original))?;
		Self::try_set_sufficient_and_weight(&original, false, None)?;

		Ok(())
	}

	/// Try deregister either 'original' or 'wrapped' system token.
	///
	/// Case - Original: `try_deregister_original` will be called.
	///
	/// Case - Wrapped: `try_deregister_wrapped` will be called.
	fn try_deregister(system_token_type: SystemTokenType) -> DispatchResult {
		match system_token_type {
			SystemTokenType::Original(original) => Self::try_deregister_original(&original),
			SystemTokenType::Wrapped(wrapped) => Self::try_deregister_wrapped(&wrapped),
		}
	}

	/// Remove value for given `original` system token id.
	///
	/// - Changes
	///
	/// `SystemTokenOnParachain`, `OrigingalSystemTokenMetadata`, `SystemTokenProperties`, `SystemTokenOnParachain`
	fn try_deregister_original(original: &SystemTokenId) -> DispatchResult {
		Self::try_remove_sys_token_for_para(original)?;
		OrigingalSystemTokenMetadata::<T>::remove(original);
		SystemTokenProperties::<T>::remove(original);
		SystemTokenOnParachain::<T>::remove(original);
		Ok(())
	}

	/// Remove value for given `wrapped` system token id.
	fn try_deregister_wrapped(wrapped: &SystemTokenId) -> DispatchResult {
		let original =
			SystemTokenOnParachain::<T>::get(&wrapped).ok_or(Error::<T>::WrappedNotRegistered)?;

		let SystemTokenId { para_id, .. } = wrapped.clone();

		Self::try_remove_sys_token_for_para(wrapped)?;
		Self::try_remove_para_id(original, para_id)?;

		SystemTokenOnParachain::<T>::remove(&wrapped);
		Ok(())
	}

	/// Try update `weight` property of `original` system token
	///
	/// State changes
	///
	/// - `SystemTokenProperties`
	fn try_update_weight_property_of_original(
		original: SystemTokenId,
		system_token_weight: SystemTokenWeight,
	) -> DispatchResult {
		SystemTokenProperties::<T>::try_mutate_exists(&original, |p| -> DispatchResult {
			let mut property = p.take().ok_or(Error::<T>::NotFound)?;
			property.system_token_weight = Some(system_token_weight);
			*p = Some(property.clone());
			Self::deposit_event(Event::<T>::SetSystemTokenWeight { original, property });
			Ok(())
		})?;

		Ok(())
	}

	/// Try push `system_token_id` for given `para_id` to `SystemTokenOnParachainByParaId`.
	///
	/// Errors
	///
	/// - `NotFound`: No value in storage(Maybe no key?).
	///
	/// - `TooManySystemTokensOnParachain`: Maximum number of elements has been reached for BoundedVec
	fn try_push_original_for_para_id(
		para_id: IbsParaId,
		orginal: &SystemTokenId,
	) -> DispatchResult {
		SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
			para_id.clone(),
			|maybe_used_system_tokens| -> Result<(), DispatchError> {
				let mut system_tokens =
					maybe_used_system_tokens.take().ok_or(Error::<T>::NotFound)?;
				system_tokens
					.try_push(*orginal)
					.map_err(|_| Error::<T>::TooManySystemTokensOnParachain)?;
				*maybe_used_system_tokens = Some(system_tokens);
				Ok(())
			},
		)?;

		Ok(())
	}

	/// Try push `para_id` for given `original` system token to `ParaIdsBySystemToken`
	///
	/// Errors
	///
	/// - `NotFound`: No value in storage(Maybe no key)?
	///
	/// - `TooManyWrapped`: Requested wrapped has reached max for the system token
	fn try_push_para_id(para_id: IbsParaId, original: &SystemTokenId) -> DispatchResult {
		ParaIdsBySystemToken::<T>::try_mutate_exists(
			original,
			|maybe_para_id_list| -> Result<(), DispatchError> {
				let mut para_ids = maybe_para_id_list.take().ok_or(Error::<T>::NotFound)?;
				para_ids.try_push(para_id).map_err(|_| Error::<T>::TooManyWrapped)?;
				*maybe_para_id_list = Some(para_ids);
				Ok(())
			},
		)?;

		Ok(())
	}

	/// Try remove `SystemTokenOnParachainByParaId` for any(`original` or `wrapped`) system token id
	fn try_remove_sys_token_for_para(sys_token_id: &SystemTokenId) -> DispatchResult {
		let SystemTokenId { para_id, .. } = sys_token_id.clone();
		// ToDo: Should we check 'len of registered system token'?
		SystemTokenOnParachainByParaId::<T>::try_mutate_exists(
			para_id,
			|maybe_system_tokens| -> Result<(), DispatchError> {
				let mut system_tokens = maybe_system_tokens.take().ok_or(Error::<T>::NotFound)?;
				if system_tokens.len() <= 1 {
					*maybe_system_tokens = None;
					return Ok(())
				}
				system_tokens.retain(|&x| x != *sys_token_id);
				*maybe_system_tokens = Some(system_tokens);
				Ok(())
			},
		)?;

		Ok(())
	}

	/// Try remove `ParaIdsBySystemToken` for system token id
	fn try_remove_para_id(sys_token_id: SystemTokenId, para_id: IbsParaId) -> DispatchResult {
		ParaIdsBySystemToken::<T>::try_mutate_exists(
			sys_token_id,
			|maybe_para_ids| -> Result<(), DispatchError> {
				let mut para_ids = maybe_para_ids.take().ok_or(Error::<T>::NotFound)?;
				para_ids.retain(|x| *x != para_id);
				*maybe_para_ids = Some(para_ids);
				Ok(())
			},
		)?;

		Ok(())
	}
}

// XCM-related internal methods
impl<T: Config> Pallet<T>
where
	<T as pallet_assets::Config>::AssetIdParameter: From<IbsAssetId>,
	AssetIdOf<T>: From<IbsAssetId>,
{
	fn try_set_sufficient_and_unlink(
		origin: &OriginFor<T>,
		system_token_id: SystemTokenId,
		is_sufficient: bool,
	) -> DispatchResult {
		let SystemTokenId { para_id, pallet_id, asset_id } = system_token_id;
		if para_id == 0u32 {
			// ToDo: Change to internal method due to 'origin'
			// Relay Chain
			pallet_assets::pallet::Pallet::<T>::set_sufficient_with_unlink_system_token(
				origin.clone(),
				asset_id.into(),
				false,
			)?;
		} else {
			// Parachain
			let encoded_call = pallet_assets::Call::<T>::set_sufficient_with_unlink_system_token {
				id: asset_id.into(),
				is_sufficient,
			}
			.encode();
			system_token_xcm_handler::try_queue_dmp::<T>(para_id, pallet_id, encoded_call)?;
		}

		Ok(())
	}

	/// Try sending DMP of call `set_sufficient_and_system_token_weight` to specific parachain.
	/// If success, destination parachain's local asset's `sufficient` state to `is_sufficient`, and set its weight
	fn try_set_sufficient_and_weight(
		system_token_id: &SystemTokenId,
		is_sufficient: bool,
		system_token_weight: Option<SystemTokenWeight>,
	) -> DispatchResult {
		let SystemTokenId { para_id, pallet_id, asset_id } = system_token_id.clone();
		let encoded_call = pallet_assets::Call::<T>::set_sufficient_and_system_token_weight {
			id: asset_id.into(),
			is_sufficient,
			system_token_weight,
		}
		.encode();
		system_token_xcm_handler::try_queue_dmp::<T>(para_id, pallet_id, encoded_call)?;

		Ok(())
	}

	fn try_update_weight_of_wrapped(
		origin: OriginFor<T>,
		wrapped: &SystemTokenId,
		system_token_weight: SystemTokenWeight,
	) -> DispatchResult {
		let SystemTokenId { para_id, pallet_id, asset_id } = wrapped.clone();

		if para_id == 0u32 {
			// Relay Chain
			// ToDo: Change to internal call
			pallet_assets::pallet::Pallet::<T>::update_system_token_weight(
				origin.clone(),
				asset_id.into(),
				system_token_weight,
			)?
		} else {
			// Parachain
			let encoded_call = pallet_assets::Call::<T>::update_system_token_weight {
				id: asset_id.into(),
				system_token_weight,
			}
			.encode();
			system_token_xcm_handler::try_queue_dmp::<T>(para_id, pallet_id, encoded_call)?;
		}

		Ok(())
	}

	fn try_create_wrapped(
		origin: OriginFor<T>,
		wrapped: SystemTokenId,
		system_token_weight: SystemTokenWeight,
	) -> DispatchResult {
		let original = <SystemTokenOnParachain<T>>::get(&wrapped).ok_or(Error::<T>::NotFound)?;
		let (_, asset_metadata) =
			OrigingalSystemTokenMetadata::<T>::get(&original).ok_or(Error::<T>::NotFound)?;
		let SystemTokenId { para_id, pallet_id, asset_id } = wrapped;
		let root: T::AccountId = PalletId(*b"infra/rt").into_account_truncating();
		if para_id == 0u32 {
			// Relay Chain
			// ToDo: Change to internal method, we don't need 'origin' here
			// ToDo: 'system_token_weight' type u64 -> u128
			pallet_assets::pallet::Pallet::<T>::force_create_with_metadata(
				origin.clone(),
				asset_id.into(),
				T::Lookup::unlookup(root),
				true,
				asset_metadata.min_balance,
				asset_metadata.name.to_vec(),
				asset_metadata.symbol.to_vec(),
				asset_metadata.decimals,
				false,
				original,
				0,
				system_token_weight,
			)?;

			// ToDo: Change to internal method, we don't need 'origin' here
			pallet_asset_link::pallet::Pallet::<T>::link_system_token(
				origin,
				0,
				asset_id.into(),
				original,
			)?;
		} else {
			// Parachain
			let encoded_call: Vec<u8> = pallet_assets::Call::<T>::force_create_with_metadata {
				id: asset_id.into(),
				owner: T::Lookup::unlookup(root),
				min_balance: asset_metadata.min_balance,
				is_sufficient: true,
				name: asset_metadata.name.to_vec(),
				symbol: asset_metadata.symbol.to_vec(),
				decimals: asset_metadata.decimals,
				is_frozen: false,
				system_token_id: original,
				asset_link_parents: 1,
				system_token_weight,
			}
			.encode();

			system_token_xcm_handler::try_queue_dmp::<T>(para_id, pallet_id, encoded_call)?;
		}

		Ok(())
	}
}

impl<T: Config> SystemTokenInterface for Pallet<T> {
	fn is_system_token(original: SystemTokenId) -> bool {
		<OrigingalSystemTokenMetadata<T>>::get(original).is_some()
	}
	fn convert_to_original_system_token(wrapped: SystemTokenId) -> Option<SystemTokenId> {
		if let Some(original) = <SystemTokenOnParachain<T>>::get(&wrapped) {
			Self::deposit_event(Event::<T>::SystemTokenConverted {
				wrapped,
				original: original.clone(),
			});
			return Some(original)
		}
		None
	}
	fn adjusted_weight(original: SystemTokenId, vote_weight: VoteWeight) -> VoteWeight {
		// updated_vote_weight = vote_weight * system_token_weight / base_system_token_weight
		if let Some(p) = <SystemTokenProperties<T>>::get(original) {
			let system_token_weight = p.system_token_weight.map_or(BASE_SYSTEM_TOKEN_WEIGHT, |w| w);
			return vote_weight.saturating_mul(system_token_weight) / BASE_SYSTEM_TOKEN_WEIGHT
		}
		vote_weight
	}
}

pub mod system_token_xcm_handler {
	use super::{Config, DispatchResult, Error, IbsPalletId, IbsParaId, Vec, Weight};
	use crate::{configuration, dmp};
	use parity_scale_codec::Encode;
	use sp_std::vec;
	use xcm::{
		opaque::{latest::prelude::*, VersionedXcm},
		v2::OriginKind,
		v3::MultiAsset,
	};

	const REF_WEIGHT: u64 = 500_000_000;
	const PROOF_WEIGHT: u64 = 20_000;

	fn encode_pallet_call(pallet_id: IbsPalletId, mut encoded_call: Vec<u8>) -> Vec<u8> {
		let mut encoded: Vec<u8> = [pallet_id].into();
		encoded.append(&mut encoded_call);
		encoded
	}

	fn transact_xcm(
		fees: MultiAsset,
		origin_kind: Option<OriginKind>,
		require_weight_at_most: Option<Weight>,
		encoded_call: Vec<u8>,
	) -> Vec<u8> {
		VersionedXcm::from(Xcm(vec![
			BuyExecution { fees: fees.into(), weight_limit: WeightLimit::Unlimited },
			Transact {
				origin_kind: origin_kind.map_or(xcm::v2::OriginKind::Superuser, |o| o),
				require_weight_at_most: require_weight_at_most
					.map_or(Weight::from_parts(REF_WEIGHT, PROOF_WEIGHT), |w| w),
				call: encoded_call.into(),
			},
		]))
		.encode()
	}

	fn build_xcm(pallet_id: IbsPalletId, call: Vec<u8>) -> Vec<u8> {
		let encoded_call = encode_pallet_call(pallet_id, call);
		let fees = MultiAsset { id: Concrete(Here.into()), fun: Fungible(10000) };
		let xcm = transact_xcm(fees, None, None, encoded_call);

		xcm
	}

	pub fn try_queue_dmp<T: Config>(
		para_id: IbsParaId,
		pallet_id: IbsPalletId,
		encoded_call: Vec<u8>,
	) -> DispatchResult {
		let config = <configuration::Pallet<T>>::config();
		let xcm = build_xcm(pallet_id, encoded_call);
		if let Err(dmp::QueueDownwardMessageError::ExceedsMaxMessageSize) =
			<dmp::Pallet<T>>::queue_downward_message(&config, IbsParaId::from(para_id).into(), xcm)
		{
			log::error!(
				target: "runtime::system_token_manager",
				"sending 'dmp' failed."
			);
			return Err(Error::<T>::DmpError.into())
		};
		Ok(())
	}
}
