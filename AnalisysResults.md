# State DAO
- **a** : _if there was no exception and the contract is not running, the contract's state is INITIALSTATE_
- **b** : _if a call to deposit is made with a msg.sender value greater than 0 then it does not raise an exception_
- **c** : _an exception is not raised even if a call to deposit is made and the balance of state_dao is greater than 20_
- **d** : _the balance of state_dao is always greater than or equal to 3_
- **e** : _the balance of state_dao is always less than or equal to 20_

## Ground Truth

||a|b|c|d|e|
|----|----|----|----|----|----|
|V1|0|0|0|1|0|
|V2|0|0|0|0|0|

## Analysis results

- **V1**

||a|b|c|d|e|
|----|----|----|----|----|----|
|NuSMV|0|1|1|1|1|
|Sym. Exec|0|1~|0|1~|0|

- **V2**

||a|b|c|d|e|
|----|----|----|----|----|----|
|NuSMV|0|1|1|0|1|
|Sym. Exec|0|1~|0|0|0|

# Airdrop
- **a** : _if a call to receive_airdrop is made and no exceptions are raised then the value for msg.sender of received_airdrop is true_
- **b** : _If a call to receive_airdrop is made from an account with received_airdrop set to 0, an exception is not raised._
- **c** : _user_balance value must always be less than or equal to airdrop_amount_

## Ground Truth

|a|b|c|
|----|----|----|
|1|0|1|

## Analysis results

||a|b|c|
|----|----|----|----|
|NuSMV|1|1|1|
|Sym. Exec|1|0|1|


# Crowdfund

- **a** : _if a call to donate is made, and no exceptions have been raised, then donors(msg.sender) is greater than 0_
- **b** : _even if a call to donate is made and the donation phase is over, an exception is not raised_
- **c** : _if a call to withdraw completes without any exceptions being raised, then the sender was the owner of the contract_
- **d** : _if a call to reclaim is made but all donors have a value of 0 then an exception is raised_
- **e** : _if a call to reclaim is made by user, and the user's donors is greater than 0 then after the donors call it is 0_

## Ground Truth

||a|b|c|d|e|
|----|----|----|----|----|----|
|V1|0|0|1|1|1|
|V2|0|0|0|1|1|

## Analysis results

- **V1**

||a|b|c|d|e|
|----|----|----|----|----|----|
|NuSMV|-|-|-|-|-|
|Sym. Exec|1~|0|1|1|1|

- **V2**


||a|b|c|d|e|
|----|----|----|----|----|----|
|NuSMV|-|-|-|-|-|
|Sym. Exec|1~|1|1|1|1|

# Auction

- **a** : _The destroy function can only be called by the owner of the contract_
- **b** : _If a call is made to the bid function and a current_frontrunner already exists, the previously deposited money is returned to it_
- **c** : _if I make a call to the bid function with a msg.value greater than current_bid then I become the new current_frontrunner_
- **d** : _if a call is made to the destroy function, all the money in the contract goes to the owner_

## Ground Truth

||a|b|c|d|
|----|----|----|----|----|
|V1|0|1|1|0|
|V2|1|1|1|1|


## Analysis results

- **V1**

||a|b|c|d|
|----|----|----|----|----|
|NuSMV|-|-|-|-|
|Sym. Exec|0|1|1|0|

- **V2**

||a|b|c|d|
|----|----|----|----|----|
|NuSMV|-|-|-|-|
|Sym. Exec|1|1|1|1~|