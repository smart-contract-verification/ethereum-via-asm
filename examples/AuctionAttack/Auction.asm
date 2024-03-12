asm Auction

import ../../lib/asmeta/StandardLibrary
import ../../lib/asmeta/CTLlibrary
import ../../lib/solidity/EVMlibrary
import ../../lib/attackers/SimpleKingOfEtherThroneAttack

signature:

	dynamic controlled currentFrontrunner : StackLayer -> User
	dynamic controlled currentBid : StackLayer -> Integer


	/* USER and METHODS */
	static auction : User
	
	static bid : Function

definitions:
	
	rule r_Save ($n in StackLayer) =
		par 
			currentFrontrunner($n) := currentFrontrunner(global_state_layer)
			currentBid($n) := currentBid(global_state_layer)
		endpar
		
	rule r_Bid = 
		if executing_function(current_layer) = bid then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[amount(current_layer) > currentBid(global_state_layer)]
				case 1 :
					if isDef(currentFrontrunner(global_state_layer)) then 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					else
						instruction_pointer(current_layer) := 4
					endif
				case 2 : 
					r_Transaction[auction, currentFrontrunner(global_state_layer), currentBid(global_state_layer), fallback]
				case 3 : 
					r_Require[call_response(current_layer+1)]
				case 4 : 
					par
						currentFrontrunner(global_state_layer) := sender(current_layer) 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 5 : 
					par
						currentBid(global_state_layer) := amount(current_layer) 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 6 : 
					r_Ret[]
			endswitch
		endif
	
	rule r_Fallback_Auction = 
		if executing_function(current_layer) = fallback then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Ret[]
			endswitch 
		endif
		
		
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
					r_Transaction[user, random_user, random_amount, random_function]
				endseq
			else
				switch executing_contract(current_layer)
					case auction :
						par 
							r_Bid[]
							r_Fallback_Auction[]
						endpar
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
	function executing_contract ($cl in StackLayer) = if $cl = 0 then user endif
	function instruction_pointer ($sl in StackLayer) = if $sl = 0 then 0 endif
	function current_layer = 0
	function transaction = false
	function balance($c in User, $n in StackLayer) = if $n = 0 then  10 endif
	function global_state_layer = 0
	function call_response($n in StackLayer) = false
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function currentBid($n in StackLayer) = if $n = 0 then 0 endif
