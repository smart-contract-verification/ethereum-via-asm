
asm KingOfTheEtherThroneAttack

import ../../Libraries/StandardLibrary
import ../../SolidityLibraries/EVMlibrary
import ../../SolidityLibraries/SimpleKingOfEtherThroneAttack

signature:
	dynamic controlled king : StackLayer -> User
	dynamic controlled claim_price : StackLayer -> MoneyAmount
	
	static kotET : User
	static initial_king : User


definitions:

	rule r_Save ($n in StackLayer) =
		par
			king($n) := king(global_state_layer) 
			claim_price($n) := claim_price(global_state_layer)
		endpar
	
	
	rule r_Kot_Fallback = 
		switch instruction_pointer(current_layer) 
			case 0: 
				r_Require[amount(current_layer) >= claim_price(global_state_layer)]
			case 1: 
				r_Transaction[kotET, king(global_state_layer), claim_price(global_state_layer), fallback]
			case 2: 
				par
					king(global_state_layer) := sender(current_layer)
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endpar
			case 3:
				par
					claim_price(global_state_layer) := claim_price(global_state_layer) + 1
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endpar
			case 4 : 
				r_Ret[]
		endswitch
		
		
//	invariant over balance : executing_contract(current_layer) = kotET and executing_function(current_layer) = fallback and instruction_pointer(current_layer) = 2 implies
//								balance(kotET, global_state_layer) = balance(kotET, global_state_layer - 1) + amount(current_layer) - claim_price(global_state_layer)
//		
		
	
	main rule r_Main =
		if transaction then 
			seq
				r_Save[global_state_layer + 1]
				r_Save_Env[global_state_layer + 1]
				r_Save_Att[global_state_layer + 1]
				global_state_layer := global_state_layer + 1
				r_Transaction_Env[]
			endseq
		else
			if current_layer = 0 then
				seq
					par 
						r_Save[0]
						r_Save_Env[0]
						global_state_layer := 0
					endpar
					r_Transaction[user, random_user, 3, random_function]
				endseq
			else
				switch executing_contract(current_layer)
					case kotET :
						r_Kot_Fallback[]
					case attacker :
						r_Attacker[]
					otherwise 
						r_Ret[]
				endswitch
			endif
		endif





default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = if $sl = 0 then none endif 
	function executing_contract ($sl in StackLayer) = if $sl = 0 then user endif
	function instruction_pointer ($sl in StackLayer) = if $sl = 0 then 0 endif
	function current_layer = 0
	function transaction = false
	function balance($c in User, $n in StackLayer) = if $n = 0 then 10 endif
	function global_state_layer = 0
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function king($n in StackLayer) = if $n = 0 then initial_king endif
	function claim_price($n in StackLayer) = if $n = 0 then 1 endif
