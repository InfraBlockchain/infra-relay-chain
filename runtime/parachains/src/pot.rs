use crate::configuration;
use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use primitives::Id as ParaId;
use sp_runtime::generic::PotVotesResult;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + configuration::Config {}

	#[pallet::error]
	pub enum Error<T> {}

	#[pallet::storage]
	pub type AggregatedPotVotes<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, PotVotesResult, ValueQuery>;
}

impl<T: Config> Pallet<T> {

	pub(crate) fn aggregate_vote_result(para: ParaId, result: PotVotesResult) {
		AggregatedPotVotes::<T>::insert(para, result);
	}
}