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
	pallet_prelude::*,
	traits::{tokens::fungibles::Balanced, OriginTrait},
	PalletId,
};
pub use pallet::*;
use sp_runtime::{
	self,
	traits::AccountIdConversion,
	types::{AssetId, SystemTokenId, SystemTokenLocalAssetProvider},
};
use sp_std::prelude::*;
use xcm::opaque::lts::{
	AssetId::Concrete, Fungibility::Fungible, Junction, Junctions::*, MultiAsset, MultiLocation,
};
use xcm_primitives::AssetMultiLocationGetter;

type AccountIdOf<T> = <T as frame_system::Config>::AccountId;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ pallet_assets::Config
		+ pallet_xcm::Config
		+ pallet_asset_link::Config
	{
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// The fungibles instance used to pay for transactions in assets.
		type Assets: Balanced<Self::AccountId> + SystemTokenLocalAssetProvider;
		type AssetMultiLocationGetter: AssetMultiLocationGetter<AssetId>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Aggrate System Token Successfully
		SystemTokenAggregated { system_token_id: SystemTokenId, amount: u128 },
	}

	#[pallet::error]
	pub enum Error<T> {}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where
		u32: From<<T as frame_system::Config>::BlockNumber>,
		<<T as frame_system::Config>::RuntimeOrigin as OriginTrait>::AccountId:
			From<AccountIdOf<T>>,
		[u8; 32]: From<<T as frame_system::Config>::AccountId>,
		u128: From<<T as pallet_assets::Config>::Balance>,
	{
		fn on_finalize(block_num: T::BlockNumber) {
			let block_num: u32 = block_num.into();
			if block_num % 10 == 0 {
				let sovereign = PalletId(*b"infrafee");
				let who: AccountIdOf<T> = sovereign.into_account_truncating();

				let system_token_asset_list =
					pallet_assets::Pallet::<T>::token_list().unwrap_or_default();
				let balances = pallet_assets::Pallet::<T>::account_balances(who.clone());
				log::info!("system_token_asset_list {:?}", system_token_asset_list);
				log::info!("balances {:?}", balances);

				for balance in balances.iter() {
					let asset_id = balance.0;
					let amount = balance.1;
					if system_token_asset_list.contains(&asset_id.clone().into()) {
						let sovereign = PalletId(*b"infrafee");
						let owner: AccountIdOf<T> = sovereign.into_account_truncating();
						let asset_multilocation =
							T::AssetMultiLocationGetter::get_asset_multi_location(
								asset_id.clone().into(),
							)
							.unwrap_or_default();
						let dest_para_id = match asset_multilocation.clone().interior() {
							X3(Junction::Parachain(para_id), _, _) => *para_id,
							_ => 1000,
						};

						let result = pallet_xcm::Pallet::<T>::limited_teleport_assets(
							<T as frame_system::Config>::RuntimeOrigin::signed(
								owner.clone().into(),
							),
							Box::new(xcm::VersionedMultiLocation::V3(MultiLocation {
								parents: 1,
								interior: X1(Junction::Parachain(dest_para_id.clone())),
							})),
							Box::new(
								Junction::AccountId32 { network: None, id: owner.clone().into() }
									.into_location()
									.into(),
							),
							Box::new(
								MultiAsset {
									id: Concrete(asset_multilocation),
									fun: Fungible(amount.clone().into()),
								}
								.into(),
							),
							0,
							xcm::v3::WeightLimit::Unlimited,
						);
					}
				}
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		<<T as frame_system::Config>::RuntimeOrigin as OriginTrait>::AccountId:
			From<AccountIdOf<T>>,
		[u8; 32]: From<<T as frame_system::Config>::AccountId>,
	{
		/// Test Function.
		#[pallet::call_index(0)]
		#[pallet::weight(1_000)]
		pub fn test(
			origin: OriginFor<T>,
			system_token_id: SystemTokenId,
			amount: u128,
		) -> DispatchResult {
			Self::teleport_system_token(system_token_id.clone(), amount.clone());
			Self::deposit_event(Event::<T>::SystemTokenAggregated {
				system_token_id: system_token_id.clone(),
				amount: amount.clone(),
			});
			Ok(())
		}
	}
	impl<T: Config> Pallet<T>
	where
		<<T as frame_system::Config>::RuntimeOrigin as OriginTrait>::AccountId:
			From<AccountIdOf<T>>,
		[u8; 32]: From<<T as frame_system::Config>::AccountId>,
	{
		pub fn teleport_system_token(system_token_id: SystemTokenId, amount: u128) {
			let sovereign = PalletId(*b"infrafee");
			let owner: AccountIdOf<T> = sovereign.into_account_truncating();
			let dest_para_id = system_token_id.para_id;
			let dest_pallet_id = system_token_id.pallet_id;
			let dest_asset_id = system_token_id.asset_id;

			let result = pallet_xcm::Pallet::<T>::limited_teleport_assets(
				<T as frame_system::Config>::RuntimeOrigin::signed(owner.clone().into()),
				Box::new(xcm::VersionedMultiLocation::V3(MultiLocation {
					parents: 1,
					interior: X1(Junction::Parachain(dest_para_id.clone())),
				})),
				Box::new(
					Junction::AccountId32 { network: None, id: owner.clone().into() }
						.into_location()
						.into(),
				),
				Box::new(
					MultiAsset {
						id: Concrete(MultiLocation {
							parents: 1,
							interior: X3(
								Junction::Parachain(dest_para_id.clone()),
								Junction::PalletInstance(dest_pallet_id as u8),
								Junction::GeneralIndex(dest_asset_id as u128),
							),
						}),
						fun: Fungible(amount.clone()),
					}
					.into(),
				),
				0,
				xcm::v3::WeightLimit::Unlimited,
			);
		}
	}
}
