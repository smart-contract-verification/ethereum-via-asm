
asm Crowdfund

import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMlibrary

signature:

	dynamic controlled end_donate : StackLayer -> Integer
	dynamic controlled goal : StackLayer -> Integer
	dynamic controlled owner : StackLayer -> User
	dynamic controlled donors : Prod(StackLayer, User) -> Integer
	
	dynamic controlled local_amount : StackLayer -> Integer
	
	
	dynamic controlled block_number : Integer -> Integer
	
	
	static crowdfund : User
	
	static donate : Function
	static withdraw : Function
	static reclaim : Function



definitions:

	
	rule r_Donate = 
		if executing_function(current_layer) = donate then
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[block_number(stage) <= end_donate(global_state_layer)]
				case 1 :
					par
						donors(global_state_layer, sender(current_layer)) := amount(current_layer)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 2 :
					r_Ret[]
			endswitch
		endif
		
	rule r_Withdraw = 
		if executing_function(current_layer) = withdraw then
			switch instruction_pointer(current_layer)
				case 0 :
					r_Require[block_number(stage) >= end_donate(global_state_layer)]
				case 1 : 
					r_Require[balance(crowdfund, global_state_layer) >= goal]
				case 2 : 
					r_Transaction[crowdfund, owner, balance(crowdfund, global_state_layer), none]
				case 3 : 
					r_Require[call_response(current_layer + 1)]
				case 4 :
					r_Ret[]
			endswitch
		endif
	
	
	rule r_Reclaim = 
		if executing_function(current_layer) = reclaim then
			switch instruction_pointer(current_layer)
				case 0 :
					r_Require[block_number(stage) >= end_donate(global_state_layer)]
				case 1 : 
					r_Require[balance(crowdfund, global_state_layer) < goal]
				case 2 : 
					r_Require[donors(global_state_layer, sender(current_layer)) > 0]
				case 3 : 
					par
						local_amount(current_layer) := donors(global_state_layer, sender(current_layer))
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 4 :
					par
						donors(global_state_layer, sender(current_layer)) := 0
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 5 : 
					r_Transaction[crowdfund, sender(current_layer), local_amount(current_layer), none]
				case 6 :
					r_Require[call_response(current_layer + 1)]
				case 7 : 
					r_Ret[]
			endswitch
		endif
	
	rule r_Fallback =
		if executing_function(current_layer) != reclaim and  executing_function(current_layer) != withdraw and  executing_function(current_layer) != donate then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
		
		
	/*
	 * INVARIANT
	 */
	 
	// after the donation phase, if the contract balance decreases then either a successful withdraw or reclaim have been performed.
	
	
	// a transaction donate is not reverted if the donation phase has not ended.
	
	
	// a transaction donate is not reverted if the donation phase has not ended and sum between the old and the current donation does not overflow.
	
	
	// calls to donate will revert if the donation phase has ended.
	
	
	// the contract balance does not increase after the end of the donation phase.
	
	
	// calls to withdraw will revert if the contract balance is less than the goal
	
	
	// only the owner can receive ETH from the contract.
	
	
	// a transaction reclaim is not reverted if the goal amount is not reached and the deposit phase has ended, and the sender has donated funds that they have not reclaimed yet
	
	
	// a transaction withdraw is not reverted if the contract balance is greater than or equal to the goal and the donation phase has ended.
	
	
	// a transaction withdraw is not reverted if the contract balance is greater than or equal to the goal, the donation phase has ended, and the receiver is an EOA.
	
	
	
	main rule r_Main = 	
	par
		if transaction then 
			par
				r_Save[global_state_layer]
				r_Transaction_Env[]
			endpar
		else
			if current_layer = 0 then
				if global_state_layer = 0 then
					r_Transaction[user, random_user(stage), random_amount(stage), random_function(stage)]
				else 
					par
						r_Save[0]
						r_Save_Env[0]
						global_state_layer := 0
					endpar
				endif
			else
				switch executing_contract(current_layer) 
					case crowdfund : 
						par 
							r_Donate[]
							r_Withdraw[]
							r_Reclaim[]
							r_Fallback[]
						endpar
					otherwise 
						r_Throw[]
				endswitch
			endif
		endif
		stage := stage + 1
	endpar
		
	
	





default init s0:

	function stage = 0

	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = if $sl = 0 then none else undef_function endif 
	function executing_contract ($cl in StackLayer) = if $cl = 0 then user else undef_user endif
	function instruction_pointer ($sl in StackLayer) = if $sl = 0 then 0 else -999999 endif
	function current_layer = 0
	function transaction = false
	function balance($c in User, $n in StackLayer) = if $n = 0 then 10 else -999999 endif
	function global_state_layer = 0
	

	function owner ($sl in StackLayer) = user
	function end_donate ($sl in StackLayer) = 10
	function goal ($sl in StackLayer) = 10
	
	function donors ($sl in StackLayer, $u in User) = -999999
	function local_amount ($sl in StackLayer) = -999999

