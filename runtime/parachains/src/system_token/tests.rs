
use sp_runtime::types::SystemTokenLocalAssetProvider;

use super::*;
use crate::{
    mock::*,
    system_token_manager::{
        *,
        Error as SystemTokenManagerError,
        Event as SystemTokenManagerEvent,
    },
};

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut storage = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let config: pallet_balances::GenesisConfig<Test> = pallet_balances::GenesisConfig::<Test> {
		balances: vec![(0, 100), (1, 98), (2, 1)],
	};
    config.assimilate_storage(&mut storage).unwrap();
    let mut ext: sp_io::TestExternalities = storage.into();
    ext.execute_with(|| System::set_block_number(1)); // For 'Event'
    ext
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

        // Scenario 1: Check `try-register_original`. Check only for possible error case
        let original_1000_50_1 = SystemTokenId::new(1000, 50, 1);
        assert_eq!(
            ParaIdSystemTokens::<Test>::get(&1000).unwrap().to_vec(),
            vec![
                original_1000_50_1,
            ]
        );

        assert_eq!(
            SystemTokenUsedParaIds::<Test>::get(&original_1000_50_1).unwrap().to_vec(),
            vec![
                1000u32
            ]
        );

        // Scenario 2: Try register 'same' system token id. Should be failed
        assert_noop!(
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
            ),
            SystemTokenManagerError::<Test>::OriginalAlreadyRegistered
        );

        System::assert_has_event(
            SystemTokenManagerEvent::OriginalSystemTokenRegistered {
                original: original_1000_50_1
            }.into()
        )
    })
}

#[test]
fn register_wrapped_system_token_works() {
    new_test_ext().execute_with(|| {
        
        let original_1000_50_1 = SystemTokenId::new(1000, 50, 1);
        let wrapped_1000_50_1 = SystemTokenId::new(2000, 50, 99);

        // Error case: Try register wrapped token before registering original tokenc
        assert_noop!(
            SystemTokenManager::register_wrapped_system_token(
                RuntimeOrigin::root(), 
                original_1000_50_1, 
                wrapped_1000_50_1
            ),
            SystemTokenManagerError::<Test>::OriginalNotRegistered
        );
        
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

        System::assert_has_event(
            SystemTokenManagerEvent::OriginalSystemTokenRegistered {
                original: original_1000_50_1
            }.into()
        );

        assert_ok!(
            SystemTokenManager::register_wrapped_system_token(
                RuntimeOrigin::root(), 
                original_1000_50_1, 
                wrapped_1000_50_1
            )
        );

        assert_eq!(
            ParaIdSystemTokens::<Test>::get(&2000).unwrap().to_vec(),
            vec![
                wrapped_1000_50_1,
            ]
        );

        assert_eq!(
            SystemTokenUsedParaIds::<Test>::get(&original_1000_50_1).unwrap().to_vec(),
            vec![
                1000u32,
                2000u32,
            ]
        );

        // Error case: Try register 'same' wrapped token
        assert_noop!(
            SystemTokenManager::register_wrapped_system_token(
                RuntimeOrigin::root(), 
                original_1000_50_1, 
                wrapped_1000_50_1
            ),
            SystemTokenManagerError::<Test>::WrappedAlreadyRegistered
        );

        System::assert_has_event(
            SystemTokenManagerEvent::WrappedSystemTokenRegistered {
                original: original_1000_50_1,
                wrapped: wrapped_1000_50_1
            }.into()
        );
    })
}

#[test]
fn register_relay_wrapped_works() {
    new_test_ext().execute_with(|| {
        let original_1000_50_1 = SystemTokenId::new(1000, 50, 1);
        let relay_wrapped_1000_50_1 = SystemTokenId::new(0, 50, 99);
        
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

        assert_ok!(
            SystemTokenManager::register_wrapped_system_token(
                RuntimeOrigin::root(), 
                original_1000_50_1, 
                relay_wrapped_1000_50_1
            )
        );

        assert_eq!(
            Assets::token_list().unwrap(),
            vec![
                99
            ]
        );
    })
}