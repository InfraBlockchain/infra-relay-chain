// Copyright 2022 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! XCM configuration for infrablockspace.

use super::{
	parachains_origin, AccountId, AllPalletsWithSystem, Balances, CouncilCollective, ParaId,
	Runtime, RuntimeCall, RuntimeEvent, RuntimeOrigin, WeightToFee, XcmPallet,
};
use frame_support::{
	match_types, parameter_types,
	traits::{Contains, Everything, Nothing},
	weights::Weight,
};
use runtime_common::{paras_registrar, xcm_sender, ToAuthor};
use sp_core::ConstU32;
use xcm::latest::prelude::*;
use xcm_builder::{
	AccountId32Aliases, AllowExplicitUnpaidExecutionFrom, AllowKnownQueryResponses,
	AllowSubscriptionsFrom, AllowTopLevelPaidExecutionFrom, BackingToPlurality,
	ChildParachainAsNative, ChildParachainConvertsVia, CurrencyAdapter as XcmCurrencyAdapter,
	FixedWeightBounds, IsConcrete, MintLocation, SignedAccountId32AsNative, SignedToAccountId32,
	SovereignSignedViaLocation, TakeWeightCredit, UsingComponents, WithComputedOrigin,
};
use xcm_executor::traits::WithOriginFilter;

parameter_types! {
	/// The location of the DOT token, from the context of this chain. Since this token is native to this
	/// chain, we make it synonymous with it and thus it is the `Here` location, which means "equivalent to
	/// the context".
	pub const TokenLocation: MultiLocation = Here.into_location();
	/// The infrablockspace network ID. This is named.
	pub const ThisNetwork: NetworkId = NetworkId::Infrablockspace;
	/// Our location in the universe of consensus systems.
	pub const UniversalLocation: InteriorMultiLocation = X1(GlobalConsensus(ThisNetwork::get()));
	/// The Checking Account, which holds any native assets that have been teleported out and not back in (yet).
	pub CheckAccount: AccountId = XcmPallet::check_account();
	/// The Checking Account along with the indication that the local chain is able to mint tokens.
	pub LocalCheckAccount: (AccountId, MintLocation) = (CheckAccount::get(), MintLocation::Local);
}

/// The canonical means of converting a `MultiLocation` into an `AccountId`, used when we want to determine
/// the sovereign account controlled by a location.
pub type SovereignAccountOf = (
	// We can convert a child parachain using the standard `AccountId` conversion.
	ChildParachainConvertsVia<ParaId, AccountId>,
	// We can directly alias an `AccountId32` into a local account.
	AccountId32Aliases<ThisNetwork, AccountId>,
);

/// Our asset transactor. This is what allows us to interact with the runtime assets from the point of
/// view of XCM-only concepts like `MultiLocation` and `MultiAsset`.
///
/// Ours is only aware of the Balances pallet, which is mapped to `TokenLocation`.
pub type LocalAssetTransactor = XcmCurrencyAdapter<
	// Use this currency:
	Balances,
	// Use this currency when it is a fungible asset matching the given location or name:
	IsConcrete<TokenLocation>,
	// We can convert the MultiLocations with our converter above:
	SovereignAccountOf,
	// Our chain's account ID type (we can't get away without mentioning it explicitly):
	AccountId,
	// We track our teleports in/out to keep total issuance correct.
	LocalCheckAccount,
>;

/// The means that we convert an XCM origin `MultiLocation` into the runtime's `Origin` type for
/// local dispatch. This is a conversion function from an `OriginKind` type along with the
/// `MultiLocation` value and returns an `Origin` value or an error.
type LocalOriginConverter = (
	// If the origin kind is `Sovereign`, then return a `Signed` origin with the account determined
	// by the `SovereignAccountOf` converter.
	SovereignSignedViaLocation<SovereignAccountOf, RuntimeOrigin>,
	// If the origin kind is `Native` and the XCM origin is a child parachain, then we can express
	// it with the special `parachains_origin::Origin` origin variant.
	ChildParachainAsNative<parachains_origin::Origin, RuntimeOrigin>,
	// If the origin kind is `Native` and the XCM origin is the `AccountId32` location, then it can
	// be expressed using the `Signed` origin variant.
	SignedAccountId32AsNative<ThisNetwork, RuntimeOrigin>,
);

parameter_types! {
	/// The amount of weight an XCM operation takes. This is a safe overestimate.
	pub const BaseXcmWeight: Weight = Weight::from_parts(1_000_000_000, 64 * 1024);
	/// Maximum number of instructions in a single XCM fragment. A sanity check against weight
	/// calculations getting too crazy.
	pub const MaxInstructions: u32 = 100;
}

/// The XCM router. When we want to send an XCM message, we use this type. It amalgamates all of our
/// individual routers.
pub type XcmRouter = (
	// Only one router so far - use DMP to communicate with child parachains.
	xcm_sender::ChildParachainRouter<Runtime, XcmPallet, ()>,
);

parameter_types! {
	pub const Dot: MultiAssetFilter = Wild(AllOf { fun: WildFungible, id: Concrete(TokenLocation::get()) });
	pub const DotForStatemint: (MultiAssetFilter, MultiLocation) = (Dot::get(), Parachain(1000).into_location());
	pub const DotForCollectives: (MultiAssetFilter, MultiLocation) = (Dot::get(), Parachain(1001).into_location());
	pub const MaxAssetsIntoHolding: u32 = 64;
}

/// infrablockspace Relay recognizes/respects the Statemint chain as a teleporter.
pub type TrustedTeleporters =
	(xcm_builder::Case<DotForStatemint>, xcm_builder::Case<DotForCollectives>);

match_types! {
	pub type OnlyParachains: impl Contains<MultiLocation> = {
		MultiLocation { parents: 0, interior: X1(Parachain(_)) }
	};
}

/// The barriers one of which must be passed for an XCM message to be executed.
pub type Barrier = (
	// Weight that is paid for may be consumed.
	TakeWeightCredit,
	AllowTopLevelPaidExecutionFrom<Everything>,
	// Messages coming from system parachains need not pay for execution.
	AllowExplicitUnpaidExecutionFrom<Everything>,
	// Subscriptions for version tracking are OK.
	AllowSubscriptionsFrom<Everything>,
);

/// A call filter for the XCM Transact instruction. This is a temporary measure until we
/// properly account for proof size weights.
///
/// Calls that are allowed through this filter must:
/// 1. Have a fixed weight;
/// 2. Cannot lead to another call being made;
/// 3. Have a defined proof size weight, e.g. no unbounded vecs in call parameters.
pub struct SafeCallFilter;
impl Contains<RuntimeCall> for SafeCallFilter {
	fn contains(call: &RuntimeCall) -> bool {
		#[cfg(feature = "runtime-benchmarks")]
		{
			if matches!(call, RuntimeCall::System(frame_system::Call::remark_with_event { .. })) {
				return true
			}
		}

		match call {
			RuntimeCall::System(
				frame_system::Call::kill_prefix { .. } | frame_system::Call::set_heap_pages { .. },
			) |
			RuntimeCall::Babe(..) |
			RuntimeCall::Timestamp(..) |
			RuntimeCall::Indices(..) |
			RuntimeCall::Balances(..) |
			RuntimeCall::Session(pallet_session::Call::purge_keys { .. }) |
			RuntimeCall::Grandpa(..) |
			RuntimeCall::ImOnline(..) |
			RuntimeCall::Democracy(
				pallet_democracy::Call::second { .. } |
				pallet_democracy::Call::vote { .. } |
				pallet_democracy::Call::emergency_cancel { .. } |
				pallet_democracy::Call::fast_track { .. } |
				pallet_democracy::Call::veto_external { .. } |
				pallet_democracy::Call::cancel_referendum { .. } |
				pallet_democracy::Call::delegate { .. } |
				pallet_democracy::Call::undelegate { .. } |
				pallet_democracy::Call::clear_public_proposals { .. } |
				pallet_democracy::Call::unlock { .. } |
				pallet_democracy::Call::remove_vote { .. } |
				pallet_democracy::Call::remove_other_vote { .. } |
				pallet_democracy::Call::blacklist { .. } |
				pallet_democracy::Call::cancel_proposal { .. },
			) |
			RuntimeCall::Council(
				pallet_collective::Call::vote { .. } |
				pallet_collective::Call::close_old_weight { .. } |
				pallet_collective::Call::disapprove_proposal { .. } |
				pallet_collective::Call::close { .. },
			) |
			RuntimeCall::TechnicalCommittee(
				pallet_collective::Call::vote { .. } |
				pallet_collective::Call::close_old_weight { .. } |
				pallet_collective::Call::disapprove_proposal { .. } |
				pallet_collective::Call::close { .. },
			) |
			RuntimeCall::PhragmenElection(
				pallet_elections_phragmen::Call::remove_voter { .. } |
				pallet_elections_phragmen::Call::submit_candidacy { .. } |
				pallet_elections_phragmen::Call::renounce_candidacy { .. } |
				pallet_elections_phragmen::Call::remove_member { .. } |
				pallet_elections_phragmen::Call::clean_defunct_voters { .. },
			) |
			RuntimeCall::TechnicalMembership(
				pallet_membership::Call::add_member { .. } |
				pallet_membership::Call::remove_member { .. } |
				pallet_membership::Call::swap_member { .. } |
				pallet_membership::Call::change_key { .. } |
				pallet_membership::Call::set_prime { .. } |
				pallet_membership::Call::clear_prime { .. },
			) |
			RuntimeCall::Treasury(..) |
			RuntimeCall::Claims(
				super::claims::Call::claim { .. } |
				super::claims::Call::mint_claim { .. } |
				super::claims::Call::move_claim { .. },
			) |
			RuntimeCall::Utility(pallet_utility::Call::as_derivative { .. }) |
			RuntimeCall::Identity(
				pallet_identity::Call::add_registrar { .. } |
				pallet_identity::Call::set_identity { .. } |
				pallet_identity::Call::clear_identity { .. } |
				pallet_identity::Call::request_judgement { .. } |
				pallet_identity::Call::cancel_request { .. } |
				pallet_identity::Call::set_fee { .. } |
				pallet_identity::Call::set_account_id { .. } |
				pallet_identity::Call::set_fields { .. } |
				pallet_identity::Call::provide_judgement { .. } |
				pallet_identity::Call::kill_identity { .. } |
				pallet_identity::Call::add_sub { .. } |
				pallet_identity::Call::rename_sub { .. } |
				pallet_identity::Call::remove_sub { .. } |
				pallet_identity::Call::quit_sub { .. },
			) |
			RuntimeCall::Vesting(..) |
			RuntimeCall::Bounties(
				pallet_bounties::Call::propose_bounty { .. } |
				pallet_bounties::Call::approve_bounty { .. } |
				pallet_bounties::Call::propose_curator { .. } |
				pallet_bounties::Call::unassign_curator { .. } |
				pallet_bounties::Call::accept_curator { .. } |
				pallet_bounties::Call::award_bounty { .. } |
				pallet_bounties::Call::claim_bounty { .. } |
				pallet_bounties::Call::close_bounty { .. },
			) |
			RuntimeCall::ChildBounties(..) |
			RuntimeCall::Hrmp(..) |
			RuntimeCall::Registrar(
				paras_registrar::Call::deregister { .. } |
				paras_registrar::Call::swap { .. } |
				paras_registrar::Call::remove_lock { .. } |
				paras_registrar::Call::reserve { .. } |
				paras_registrar::Call::add_lock { .. },
			) |
			RuntimeCall::XcmPallet(pallet_xcm::Call::limited_reserve_transfer_assets {
				..
			}) => true,
			_ => false,
		}
	}
}

pub struct XcmConfig;
impl xcm_executor::Config for XcmConfig {
	type RuntimeCall = RuntimeCall;
	type XcmSender = XcmRouter;
	type AssetTransactor = LocalAssetTransactor;
	type OriginConverter = LocalOriginConverter;
	// infrablockspace Relay recognises no chains which act as reserves.
	type IsReserve = ();
	type IsTeleporter = TrustedTeleporters;
	type UniversalLocation = UniversalLocation;
	type Barrier = Barrier;
	type Weigher = FixedWeightBounds<BaseXcmWeight, RuntimeCall, MaxInstructions>;
	// The weight trader piggybacks on the existing transaction-fee conversion logic.
	type Trader =
		UsingComponents<WeightToFee, TokenLocation, AccountId, Balances, ToAuthor<Runtime>>;
	type ResponseHandler = XcmPallet;
	type AssetTrap = XcmPallet;
	type AssetLocker = ();
	type AssetExchanger = ();
	type AssetClaims = XcmPallet;
	type SubscriptionService = XcmPallet;
	type PalletInstancesInfo = AllPalletsWithSystem;
	type MaxAssetsIntoHolding = MaxAssetsIntoHolding;
	type FeeManager = ();
	// No bridges yet...
	type MessageExporter = ();
	type UniversalAliases = Nothing;
	type CallDispatcher = WithOriginFilter<SafeCallFilter>;
	type SafeCallFilter = SafeCallFilter;
}

parameter_types! {
	pub const CouncilBodyId: BodyId = BodyId::Executive;
}

#[cfg(feature = "runtime-benchmarks")]
parameter_types! {
	pub ReachableDest: Option<MultiLocation> = Some(Parachain(1000).into());
}

/// Type to convert a council origin to a Plurality `MultiLocation` value.
pub type CouncilToPlurality = BackingToPlurality<
	RuntimeOrigin,
	pallet_collective::Origin<Runtime, CouncilCollective>,
	CouncilBodyId,
>;

/// Type to convert an `Origin` type value into a `MultiLocation` value which represents an interior location
/// of this chain.
pub type LocalOriginToLocation = (
	// We allow an origin from the Collective pallet to be used in XCM as a corresponding Plurality of the
	// `Unit` body.
	CouncilToPlurality,
	// And a usual Signed origin to be used in XCM as a corresponding AccountId32
	SignedToAccountId32<RuntimeOrigin, AccountId, ThisNetwork>,
);

impl pallet_xcm::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	// Only allow the council to send messages.
	type SendXcmOrigin = xcm_builder::EnsureXcmOrigin<RuntimeOrigin, CouncilToPlurality>;
	type XcmRouter = XcmRouter;
	// Anyone can execute XCM messages locally...
	type ExecuteXcmOrigin = xcm_builder::EnsureXcmOrigin<RuntimeOrigin, LocalOriginToLocation>;
	// ...but they must match our filter, which rejects all.
	type XcmExecuteFilter = Nothing; // == Deny All
	type XcmExecutor = xcm_executor::XcmExecutor<XcmConfig>;
	type XcmTeleportFilter = Everything; // == Allow All
	type XcmReserveTransferFilter = Everything; // == Allow All
	type Weigher = FixedWeightBounds<BaseXcmWeight, RuntimeCall, MaxInstructions>;
	type UniversalLocation = UniversalLocation;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	const VERSION_DISCOVERY_QUEUE_SIZE: u32 = 100;
	type AdvertisedXcmVersion = pallet_xcm::CurrentXcmVersion;
	type Currency = Balances;
	type CurrencyMatcher = ();
	type TrustedLockers = ();
	type SovereignAccountOf = SovereignAccountOf;
	type MaxLockers = ConstU32<8>;
	type WeightInfo = crate::weights::pallet_xcm::WeightInfo<Runtime>;
	#[cfg(feature = "runtime-benchmarks")]
	type ReachableDest = ReachableDest;
}
