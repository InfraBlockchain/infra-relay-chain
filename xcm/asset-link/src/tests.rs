use crate::{mock::*, Error};
use frame_support::{assert_noop, assert_ok};
use xcm::latest::prelude::*;

#[test]
fn register_reserve_asset_works() {
	new_test_ext().execute_with(|| {
		let statemine_para_id = StatemineParaIdInfo::get();
		let statemine_assets_pallet = StatemineAssetsInstanceInfo::get();
		let statemine_asset_id = StatemineAssetIdInfo::get();

		let statemine_asset_multi_location = MultiLocation {
			parents: 1,
			interior: X3(
				Parachain(statemine_para_id),
				PalletInstance(statemine_assets_pallet),
				GeneralIndex(statemine_asset_id),
			),
		};

		assert_ok!(AssetLink::link_system_token(
			RuntimeOrigin::root(),
			LOCAL_ASSET_ID,
			statemine_asset_multi_location.clone(),
		));

		let read_asset_multi_location = AssetLink::asset_id_multilocation(LOCAL_ASSET_ID)
			.expect("error reading AssetIdMultiLocation");
		assert_eq!(read_asset_multi_location, statemine_asset_multi_location);

		let read_asset_id = AssetLink::asset_multilocation_id(&statemine_asset_multi_location)
			.expect("error reading AssetMultiLocationId");
		assert_eq!(read_asset_id, LOCAL_ASSET_ID);

		assert_noop!(
			AssetLink::link_system_token(
				RuntimeOrigin::root(),
				LOCAL_ASSET_ID,
				statemine_asset_multi_location,
			),
			Error::<Test>::AssetAlreadyRegistered
		);
	});
}

#[test]
fn unregister_reserve_asset_works() {
	new_test_ext().execute_with(|| {
		let statemine_para_id = StatemineParaIdInfo::get();
		let statemine_assets_pallet = StatemineAssetsInstanceInfo::get();
		let statemine_asset_id = StatemineAssetIdInfo::get();

		let statemine_asset_multi_location = MultiLocation {
			parents: 1,
			interior: X3(
				Parachain(statemine_para_id),
				PalletInstance(statemine_assets_pallet),
				GeneralIndex(statemine_asset_id),
			),
		};

		assert_ok!(AssetLink::link_system_token(
			RuntimeOrigin::root(),
			LOCAL_ASSET_ID,
			statemine_asset_multi_location.clone(),
		));

		assert_ok!(AssetLink::unlink_system_token(RuntimeOrigin::root(), LOCAL_ASSET_ID));

		assert!(AssetLink::asset_id_multilocation(LOCAL_ASSET_ID).is_none());
		assert!(AssetLink::asset_multilocation_id(statemine_asset_multi_location.clone()).is_none());
	});
}
