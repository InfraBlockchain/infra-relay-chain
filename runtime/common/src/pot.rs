use frame_support::traits::pot::VoteInfoHandler;
use sp_runtime::generic::{VoteAccountId, VoteWeight, VoteAssetId, PotVotes};
use sp_std::prelude::*;
pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
        VoteCollected {
            candidate: VoteAccountId,
            asset_id: VoteAssetId,
            weight: VoteWeight,
        },
        VoteWeightUpdated {
            candidate: VoteAccountId, 
            asset_id: VoteAssetId,
        }
    }

	#[pallet::error]
	pub enum Error<T> {}

    /// The vote weight of a specific account for a specific asset.
	#[pallet::storage]
	pub(super) type CollectedPotVotes<T: Config> = StorageValue<_, PotVotes, OptionQuery>;
}

impl<T: Config> VoteInfoHandler for Pallet<T> {
	type VoteAccountId = VoteAccountId;
	type VoteAssetId = VoteAssetId;
	type VoteWeight = VoteWeight;

	fn update_pot_vote(who: VoteAccountId, asset_id: VoteAssetId, vote_weight: VoteWeight) {
		Self::do_update_pot_vote(asset_id, who, vote_weight);
	}
}

impl<T: Config> Pallet<T> {
	/// Update vote weight for given (asset_id, candidate)
	fn do_update_pot_vote(
		vote_asset_id: VoteAssetId,
		vote_account_id: VoteAccountId,
		vote_weight: VoteWeight,
	) {
		let pot_votes = if let Some(mut old) = CollectedPotVotes::<T>::get() {
			old.update_vote_weight(vote_asset_id.clone(), vote_account_id.clone(), vote_weight);
            Pallet::<T>::deposit_event(Event::<T>::VoteWeightUpdated {
                candidate: vote_account_id,
                asset_id: vote_asset_id,
            });
			old
		} else {
            Pallet::<T>::deposit_event(Event::<T>::VoteCollected {
                candidate: vote_account_id.clone(),
                asset_id: vote_asset_id.clone(),
                weight: vote_weight.clone(),
            });
			PotVotes::new(vote_asset_id, vote_account_id, vote_weight)
		};
		CollectedPotVotes::<T>::put(pot_votes);
	}
}