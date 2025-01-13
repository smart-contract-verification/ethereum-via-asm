asm Bank





import ../../lib/asmeta/CTLlibrary
import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMlibrary



signature:	

	/* CONTRACT ATTRIBUTES */
	dynamic controlled balances : Prod(User, StackLayer) -> MoneyAmount 
	
	
	/* FUNCTIONS PARAMETERS */
	dynamic controlled withdrawal : Integer -> MoneyAmount
	dynamic controlled value_withdraw : StackLayer -> MoneyAmount 
	
	
	dynamic controlled old_balance : Integer
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static dao : User
	
	static undef_user : User
	static undef_function : Function
	
	static deposit : Function
	static withdraw : Function 

	
	
definitions:
	
	/* --------------------------------------------BANK CONTRACT IMPLEMENTATION-------------------------------------------- */

	rule r_Save ($n in StackLayer) =
		forall $u in User with true do 
			balances($u, $n) := balances($u, global_state_layer)


	/* 
	 * DEPOSIT FUNCTION RULE
	 */
	 
	rule r_Deposit =
		if executing_function(current_layer) = deposit then 
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						balances(sender(current_layer), global_state_layer) := balances(sender(current_layer), global_state_layer) + amount(current_layer)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 : 
					r_Ret[]
			endswitch
		endif
		
		
	/* 
	 * WITHDARW FUNCTION RULE
	 */
	 
	rule r_Withdraw = 
		if executing_function(current_layer) = withdraw then
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						value_withdraw(current_layer) := withdrawal(stage)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 : 
					r_Require[value_withdraw(current_layer) > 0]
				case 2 : 
					r_Require[value_withdraw(current_layer) <= balance(sender(current_layer), global_state_layer)]
				case 3 : 
					par
						balances(sender(current_layer), global_state_layer) := balances(sender(current_layer), global_state_layer) - value_withdraw(current_layer)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 4 :
					r_Transaction[dao, sender(current_layer), value_withdraw(current_layer), none]
				case 5 :
					r_Require[call_response(current_layer)]
				case 6 :
					r_Ret[]
			endswitch
		endif
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	 
	rule r_Fallback =
		if executing_function(current_layer) != deposit and  executing_function(current_layer) != withdraw then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */

	// after a successful deposit(), the ETH balance of the contract is increased by msg.value.
	invariant over balance : (executing_function(current_layer) = deposit and instruction_pointer(current_layer) = 1) implies (balance(dao, global_state_layer) = old_balance + amount(current_layer))
	
	// a deposit call does not revert if msg.value is less or equal to the ETH balance of msg.sender.
	invariant over call_response : (executing_function(current_layer) = deposit and instruction_pointer(current_layer) = 1) implies (call_response(current_layer))
	
	// a deposit call reverts if msg.value is greater than the ETH balance of msg.sender
	invariant over call_response : (executing_function(current_layer) = deposit) implies (call_response(current_layer))
	
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 	
		if transaction then 
			par
				r_Save[global_state_layer]
				r_Transaction_Env[]
				old_balance := balance(receiver(current_layer + 1), global_state_layer)
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
					case dao : 
						par 
							r_Deposit[]
							r_Withdraw[]
							r_Fallback[]
						endpar
					otherwise 
						r_Ret[]
				endswitch
			endif
		endif
			






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
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function balances($c in User, $n in StackLayer) = if $n = 0 then 1 else -999999 endif
		

	
	
