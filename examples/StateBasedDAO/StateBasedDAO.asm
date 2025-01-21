asm StateBasedDAO


import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMlibrary



signature:	
	enum domain State = {INTRANSITION, INITIALSTATE}

	/* CONTRACT ATTRIBUTES */
	dynamic controlled customer_balance : User -> MoneyAmount 
	
	dynamic controlled state : State
	
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static state_dao : User
	
	static deposit : Function
	static withdraw : Function 
	
	
	
definitions:
	
	
	
	/* --------------------------------------------CONTRACT IMPLEMENTATION-------------------------------------------- */

	/* 
	 * DEPOSIT FUNCTION RULE
	 */
	 
	rule r_Deposit =
		if executing_function(current_layer) = deposit then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[state = INITIALSTATE]
				case 1 : 
					par 
						state := INTRANSITION
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 2 : 
					r_Require[balance(executing_contract(current_layer)) < 20]
				case 3 : 
					par
						customer_balance(sender(current_layer)) := customer_balance(sender(current_layer)) + amount(current_layer)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 4 : 
					par
						state := INITIALSTATE
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 5 : 
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
					r_Require[state = INITIALSTATE]
				case 1 : 
					par 
						state := INTRANSITION
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 2 : 
					r_Require[customer_balance(sender(current_layer)) > 0]
				case 3 : 
					r_Transaction[state_dao, sender(current_layer), customer_balance(sender(current_layer)), none]
				case 4 :
					par
						customer_balance(sender(current_layer)) := 0
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 5 :
					r_Ret[]
				case 6 : 
					par
						state := INITIALSTATE
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 7 :
					r_Ret[]
			endswitch
		endif
		
	
	
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
	
	invariant over state : current_layer = 0 implies state = INITIALSTATE
	
	
//	/*
//	 * CTLSPEC
//	 */
//	CTLSPEC balance(state_dao) >= 20 implies ef(balance(state_dao) < 20)
//	CTLSPEC state = INTRANSITION implies ef(state = INITIALSTATE)

		
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 	
		if current_layer = 0 then
			r_Transaction[user, random_user, random_amount, random_function]
		else
			if executing_contract(current_layer) = state_dao then
				par 
					r_Deposit[]
					r_Withdraw[]
					r_Fallback[]
				endpar
			endif
		endif







default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = none
	function executing_contract ($cl in StackLayer) = user
	function instruction_pointer ($sl in StackLayer) = 0
	function current_layer = 0
	function balance($c in User) = 10
	function destroyed($u in User) = false
	function payable($f in Function) = 
		switch $f
			case deposit : true
			case withdraw : false
			case none : true
			otherwise false
		endswitch
	function exception = false

	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function customer_balance($c in User) = 0
	function state = INITIALSTATE
		

	
	
