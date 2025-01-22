# State DAO
- **a** : _if there was no exception and the contract is not running, the contract's state is INITIALSTATE_
- **b** : _if a call to deposit is made with a msg.sender value greater than 0 then it does not raise an exception_
- **c** : _an exception is not raised even if a call to deposit is made and the balance of state_dao is greater than 20_
- **d** : _the balance of state_dao is always greater than or equal to 3_
- **e** : _the balance of state_dao is always less than or equal to 20_

## Ground Truth

|a|b|c|d|e|
|----|----|----|----|----|
|0|0|0|1|0|

## Analysis results

||a|b|c|d|e|
|----|----|----|----|----|----|
|NuSMV|0|1|1|1|1|
|Sym. Exec|0|1|0|1|0|