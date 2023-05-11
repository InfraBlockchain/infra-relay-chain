use crate::configuration;
use primitives::Id as ParaId;
use sp_runtime::generic::PotVotesResult;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {

	use super::*;
	use frame_support::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + configuration::Config {
		type RuntimeEvent: From<Event> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::error]
	pub enum Error<T> {}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event {
		VoteCollected { para: ParaId, vote: PotVotesResult },
	}

	#[pallet::storage]
	pub type AggregatedPotVotes<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, PotVotesResult, ValueQuery>;
}

impl<T: Config> Pallet<T> {
	pub(crate) fn aggregate_vote_result(para: ParaId, result: PotVotesResult) {
		AggregatedPotVotes::<T>::insert(&para, result.clone());
		Self::deposit_event(Event::VoteCollected { para, vote: result })
	}
}
