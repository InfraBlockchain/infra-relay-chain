
use super::*;
use crate::{
    mock::*,
    system_token_manager::*,
};

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut storage = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let config: pallet_balances::GenesisConfig<Test> = pallet_balances::GenesisConfig::<Test> {
		balances: vec![(0, 100), (1, 98), (2, 1)],
	};
    config.assimilate_storage(&mut storage).unwrap();
    storage.into()
}

pub fn mock_system_token(system_token_id: SystemTokenId) -> (
    SystemTokenId, 
    SystemTokenWeight, 
    Vec<u8>, // issuer
    Vec<u8>, // description
    Vec<u8>, // url
    Vec<u8>, // name
    Vec<u8>, // symbol
    u8,
    u128
) {
    (
        system_token_id,
        1_000,
        "BCLABS".into(),
        "BCLABS".into(),
        "BCLABS".into(),
        "BCLABS".into(),
        "IUSD".into(),
        4,
        1_000
    )
}

#[test]
fn genesis_works() {
    new_test_ext().execute_with(|| {
        assert_eq!(Balances::free_balance(0),100u128);
        assert_eq!(Balances::free_balance(1), 98u128);
        assert_eq!(Balances::free_balance(2), 1u128);
    })
}

#[test]
fn only_root_can_call_works() {
    new_test_ext().execute_with(|| {
        // Scenario 1: 'Root(Privileged) origin is required
        assert_noop!(
            SystemTokenManager::register_system_token(
                RuntimeOrigin::signed(1u64),
                SystemTokenId::new(1000, 50, 1),
                1_000,
                "BCLABS".into(),
                "BCLABS".into(),
                "BCLABS".into(),
                "BCLABS".into(),
                "IUSD".into(),
                4,
                1_000
            ),
            BadOrigin,
        );
    })
}

#[test]
fn register_system_token_works() {
    new_test_ext().execute_with(|| {
        // Scenario 1: 'Root(Privileged) origin is required
        assert_ok!(
            SystemTokenManager::register_system_token(
                RuntimeOrigin::root(),
                SystemTokenId::new(1000, 50, 1),
                1_000,
                "BCLABS".into(),
                "BCLABS".into(),
                "BCLABS".into(),
                "BCLABS".into(),
                "IUSD".into(),
                4,
                1_000
            )
        );

        assert_eq!(
            ParaIdSystemTokens::<Test>::get(&1000).unwrap().to_vec(),
            vec![
                SystemTokenId { para_id: 1001, pallet_id: 50, asset_id: 1}
            ]
        );
    })
}