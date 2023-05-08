//! InfrablockSpace runtime. This can be compiled with `#[no_std]`, ready for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]
// `construct_runtime!` does a lot of recursion and requires us to increase the limit to 256.
#![recursion_limit = "256"]

// InfraBlockspace Primivites types
use primitives::{
	AccountId, AccountIndex, Balance, BlockNumber, CandidateEvent, CommittedCandidateReceipt,
	CoreState, GroupRotationInfo, Hash, Id as ParaId, InboundDownwardMessage, InboundHrmpMessage,
	Moment, Nonce, OccupiedCoreAssumption, PersistedValidationData, ScrapedOnChainVotes,
	SessionInfo, Signature, ValidationCode, ValidationCodeHash, ValidatorId, ValidatorIndex,
	LOWEST_PUBLIC_ID,
};

// Common feature for InfraBs Runtime
use runtime_common::{
	auctions, claims, crowdloan, impl_runtime_weights, impls::DealWithFees, paras_registrar,
	prod_or_fast, slots, BalanceToU256, BlockHashCount, BlockLength, CurrencyToVote,
	SlowAdjustingFeeUpdate, U256ToBalance, pot as relay_pot,
};

// For Runtime
use infrablockspace_runtime_constants::{currency::*, fee::*, time::*};
use parity_scale_codec::{Decode, Encode, MaxEncodedLen};
use sp_core::{ConstU128, OpaqueMetadata};
use sp_io::storage;
use sp_runtime::{
	create_runtime_str, generic, impl_opaque_keys,
	traits::{
		AccountIdLookup, BlakeTwo256, Block as BlockT, ConvertInto, Extrinsic as ExtrinsicT,
		OpaqueKeys, SaturatedConversion, Verify,
	},
	ApplyExtrinsicResult, KeyTypeId, Permill,
};
use sp_std::{cmp::Ordering, collections::btree_map::BTreeMap, prelude::*};
use sp_version::RuntimeVersion;
pub type AssetId = u32;

// Frame Imports
use frame_support::{
	construct_runtime, parameter_types,
	traits::{
		tokens::fungibles::{Balanced, CreditOf},
		AsEnsureOriginWithArg, ConstU32, Contains, EitherOf, EitherOfDiverse, InstanceFilter,
		KeyOwnerProofSystem, LockIdentifier, PrivilegeCmp, StorageMapShim, WithdrawReasons,
	},
	weights::ConstantMultiplier,
	PalletId,
};
use frame_system::{EnsureRoot, EnsureRootWithSuccess, EnsureSigned};
use pallet_asset_tx_payment::{FungiblesAdapter, HandleCredit};
use pallet_assets::{AssetsCallback, BalanceToAssetBalance};
use pallet_transaction_payment::CurrencyAdapter;

// Weights used in the Runtime.
mod weights;

// Basic weights for InfraBs Runtime
impl_runtime_weights!(infrablockspace_runtime_constants);

// For Parachains
use runtime_parachains::{
	configuration as parachains_configuration, disputes as parachains_disputes,
	dmp as parachains_dmp, hrmp as parachains_hrmp, inclusion as parachains_inclusion,
	initializer as parachains_initializer, origin as parachains_origin, paras as parachains_paras,
	paras_inherent as parachains_paras_inherent, reward_points as parachains_reward_points,
	runtime_api_impl::v2 as parachains_runtime_api_impl, scheduler as parachains_scheduler,
	session_info as parachains_session_info, shared as parachains_shared, ump as parachains_ump,
};

/// Runtime version (InfraBs).
#[sp_version::runtime_version]
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: create_runtime_str!("infrabs"),
	impl_name: create_runtime_str!("bclabs-infrabs"),
	authoring_version: 2,
	spec_version: 1000, // ToDO: Check this if needed
	impl_version: 0,
	#[cfg(not(feature = "disable-runtime-api"))]
	apis: RUNTIME_API_VERSIONS,
	#[cfg(feature = "disable-runtime-api")]
	apis: sp_version::create_apis_vec![[]],
	transaction_version: 19,
	state_version: 0,
};

parameter_types! {
	pub const Version: RuntimeVersion = VERSION;
	pub const SS58Prefix: u8 = 2;
}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = BlockLength;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = Nonce;
	type BlockNumber = BlockNumber;
	type Hash = Hash;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = AccountIdLookup<AccountId, ()>;
	type Header = generic::Header<BlockNumber, BlakeTwo256>;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = BlockHashCount;
	type DbWeight = RocksDbWeight;
	type Version = Version;
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = weights::frame_system::WeightInfo<Runtime>;
	type SS58Prefix = SS58Prefix;
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

// Config for system currency

parameter_types! {
	pub const ExistentialDeposit: Balance = EXISTENTIAL_DEPOSIT;
	pub const MaxLocks: u32 = 50;
	pub const MaxReserves: u32 = 50;
}

impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = MaxLocks;
	type MaxReserves = MaxReserves;
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = weights::pallet_balances::WeightInfo<Runtime>;
}

parameter_types! {
	pub const RemoveItemsLimit: u32 = 5;
	pub const ApprovalDeposit: Balance = 1 * DOLLARS;
	pub const AssetDeposit: Balance = 1 * DOLLARS;
	pub const AssetAccountDeposit: Balance = 1 * DOLLARS;
	pub const MetadataDepositBase: Balance = 1 * DOLLARS;
	pub const MetadataDepositPerByte: Balance = 1 * DOLLARS;
	pub const StringLimit: u32 = 50;
}

// ToDo: CallBackHandle should be changed to something else
pub struct AssetsCallbackHandle;
impl AssetsCallback<AssetId, AccountId> for AssetsCallbackHandle {
	fn created(_id: &AssetId, _owner: &AccountId) {
		storage::set(b"asset_created", &().encode());
	}

	fn destroyed(_id: &AssetId) {
		storage::set(b"asset_destroyed", &().encode());
	}
}

impl pallet_assets::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type ApprovalDeposit = ApprovalDeposit;
	type Balance = Balance;
	type RemoveItemsLimit = RemoveItemsLimit;
	type AssetId = AssetId;
	type AssetIdParameter = AssetId;
	type AssetAccountDeposit = AssetAccountDeposit;
	type Currency = Balances;
	type CreateOrigin = AsEnsureOriginWithArg<EnsureSigned<AccountId>>;
	type ForceOrigin = EnsureRoot<AccountId>;
	type AssetDeposit = AssetDeposit;
	type MetadataDepositBase = MetadataDepositBase;
	type MetadataDepositPerByte = MetadataDepositPerByte;
	type CallbackHandle = AssetsCallbackHandle;
	type StringLimit = StringLimit;
	type Freezer = ();
	type Extra = ();
	type WeightInfo = ();
}

// Config for tx payment
parameter_types! {
	pub const TransactionByteFee: Balance = 10 * MILLICENTS;
	/// This value increases the priority of `Operational` transactions by adding
	/// a "virtual tip" that's equal to the `OperationalFeeMultiplier * final_fee`.
	pub const OperationalFeeMultiplier: u8 = 5;
}

impl pallet_transaction_payment::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type OnChargeTransaction = CurrencyAdapter<Balances, DealWithFees<Runtime>>;
	type OperationalFeeMultiplier = OperationalFeeMultiplier;
	type WeightToFee = WeightToFee;
	type LengthToFee = ConstantMultiplier<Balance, TransactionByteFee>;
	type FeeMultiplierUpdate = SlowAdjustingFeeUpdate<Self>;
}

// For Pallet Asset Tx Payment
// ToDo: Check if this is needed
pub struct CreditToBlockAuthor;
impl HandleCredit<AccountId, Assets> for CreditToBlockAuthor {
	fn handle_credit(credit: CreditOf<AccountId, Assets>) {
		if let Some(author) = pallet_authorship::Pallet::<Runtime>::author() {
			// What to do in case paying the author fails (e.g. because `fee < min_balance`)
			// default: drop the result which will trigger the `OnDrop` of the imbalance.
			let _ = <Assets as Balanced<AccountId>>::resolve(&author, credit);
		}
	}
}

impl pallet_asset_tx_payment::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type Fungibles = Assets;
	type OnChargeAssetTransaction = FungiblesAdapter<
		BalanceToAssetBalance<Balances, Runtime, ConvertInto>,
		CreditToBlockAuthor,
	>;
}

// Config for consensus support
// ToDo: Should be filled with something
impl pallet_authorship::Config for Runtime {
	type FindAuthor = ();
	type EventHandler = ();
}

// Config for governance support
parameter_types! {
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const ProposalBondMinimum: Balance = 100 * DOLLARS;
	pub const ProposalBondMaximum: Balance = 500 * DOLLARS;
	pub const SpendPeriod: BlockNumber = 24 * DAYS;
	pub const MaxApprovals: u32 = 100;
	pub const RootSpendOriginMaxAmount: Balance = Balance::MAX;
}

// ToDo: `ApproveOrigin` `RejectOrigin` should be changed to something else
impl pallet_treasury::Config for Runtime {
	type PalletId = TreasuryPalletId;
	type Currency = Balances;
	type ApproveOrigin = EnsureRoot<AccountId>;
	type RejectOrigin = EnsureRoot<AccountId>;
	type RuntimeEvent = RuntimeEvent;
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type ProposalBondMaximum = ProposalBondMaximum;
	type MaxApprovals = MaxApprovals;
	type SpendPeriod = SpendPeriod;
	type SpendOrigin = EnsureRootWithSuccess<AccountId, RootSpendOriginMaxAmount>;
	type OnSlash = ();
	type Burn = ();
	type BurnDestination = ();
	type SpendFunds = ();
	type WeightInfo = ();
}

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = primitives::Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Storage, Config, Event<T>} = 0,
		// Runtime Primitives
		// Balance, Fee payment, etc..
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>} = 5,
		Assets: pallet_assets::{Pallet, Call, Storage, Config<T>, Event<T>} = 6,
		TransactionPayment: pallet_transaction_payment::{Pallet, Storage, Event<T>} = 32,
		AssetTransactionPayment: pallet_asset_tx_payment::{Pallet, Storage, Event<T>} = 33,
		// Consensus support.
		// Authorship must be before session in order to note author in the correct session and era
		Authorship: pallet_authorship::{Pallet, Storage} = 7,
		// Governance support
		Treasury: pallet_treasury::{Pallet, Call, Storage, Config, Event<T>} = 19,
	}
}

/// All migrations that will run on the next runtime upgrade.
///
/// Should be cleared after every release.
pub type Migrations = ();
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic =
	generic::UncheckedExtrinsic<Address, RuntimeCall, Signature, SignedExtra>;
// Orchestra frame for InfraBlockspace Runtime
pub type Executive = frame_executive::Executive<
	Runtime,
	Block,
	frame_system::ChainContext<Runtime>,
	Runtime,
	AllPalletsWithSystem,
	Migrations, // Runtime Upgrade
>;

/// The address format for describing accounts.
pub type Address = sp_runtime::MultiAddress<AccountId, ()>;
/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;
/// `BlockId` type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// The `SignedExtension` to the basic transaction logic.
pub type SignedExtra = (
	frame_system::CheckNonZeroSender<Runtime>,
	frame_system::CheckSpecVersion<Runtime>,
	frame_system::CheckTxVersion<Runtime>,
	frame_system::CheckGenesis<Runtime>,
	frame_system::CheckMortality<Runtime>,
	frame_system::CheckNonce<Runtime>,
	frame_system::CheckWeight<Runtime>,
	// Fee in InfraBs will be paid in fiat-based token
	pallet_asset_tx_payment::ChargeAssetTxPayment<Runtime>, // Vote from extrinsic will be checked
	                                                        // pallet_pot::CheckVote<Runtime>
);

/// The payload being signed in the transactions.
pub type SignedPayload = generic::SignedPayload<RuntimeCall, SignedExtra>;

#[cfg(not(feature = "disable-runtime-api"))]
sp_api::impl_runtime_apis! {
	impl sp_api::Core<Block> for Runtime {
		fn version() -> RuntimeVersion {
			VERSION
		}

		fn execute_block(block: Block) {
			Executive::execute_block(block);
		}

		fn initialize_block(header: &<Block as BlockT>::Header) {
			Executive::initialize_block(header)
		}
	}

	impl sp_api::Metadata<Block> for Runtime {
		fn metadata() -> OpaqueMetadata {
			OpaqueMetadata::new(Runtime::metadata().into())
		}
	}

	impl block_builder_api::BlockBuilder<Block> for Runtime {
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult {
			Executive::apply_extrinsic(extrinsic)
		}

		fn finalize_block() -> <Block as BlockT>::Header {
			Executive::finalize_block()
		}

		fn inherent_extrinsics(data: inherents::InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
			data.create_extrinsics()
		}

		fn check_inherents(
			block: Block,
			data: inherents::InherentData,
		) -> inherents::CheckInherentsResult {
			data.check_extrinsics(&block)
		}
	}
}
