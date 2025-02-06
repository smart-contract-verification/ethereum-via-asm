asm StateBasedDAOflattenedSymbolic_V2




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrarySymbolic


signature:	
	
	
	/* --------------------------------------------CONTRACT MODEL DOMANIS-------------------------------------------- */
	
	enum domain State = {INTRANSITION, INITIALSTATE}
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	/* CONTRACT ATTRIBUTES */
	dynamic controlled customer_balance : User -> Integer 
	
	dynamic controlled state : State
	
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static state_dao : User
	
	static deposit : Function
	static withdraw : Function 
	
	


	
	
definitions:
	
	
	/* --------------------------------------------CONTRACT MODEL-------------------------------------------- */

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
					r_Require[balance(state_dao) <= 12]
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
					let ($cl = current_layer) in
						let ($r = sender($cl)) in
							let ($f = none) in 
								let ($n = customer_balance($r)) in
									r_Transaction[state_dao, $r, $n - 2, $f]
								endlet
							endlet
						endlet
					endlet
				case 4 :
					if not exception then
						par
							customer_balance(sender(current_layer)) := 0
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 5 : 
					par
						state := INITIALSTATE
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 6 :
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
	 * INVARIANT S_30
	 */
	 
	// if there was no exception and the contract is not running, the contract's state is INITIALSTATE - 
	invariant over state : ((current_layer = 0 and not exception) implies (state = INITIALSTATE))
	
	//se viene fatta una chiamata a deposit con un valore di msg.sender maggiore di 0 allora non alza un eccezione - ~ S_8
	invariant over exception : ((executing_contract(1) = state_dao) and (executing_function(1) = deposit) and (amount(1) > 0) and state = INITIALSTATE) implies (exception = false)
	
	// non viene alzata una eccezione anche se viene fatta una chiamata a deposit e il balance di state_dao è maggiore o uguale di 12 - S_4
	invariant over exception : ((executing_contract(1) = state_dao and executing_function(1) = deposit and balance(state_dao) >= 12) implies (exception = false))
	
	// esiste sempre almeno un balance che sia maggiore del corrispettivo customer_balance - ~ S_1
	invariant over balance : (exist $u in User with (not is_contract($u)) and customer_balance($u) < balance($u))
	
	// il balance di state_dao è sempre minore o uguale a 12 -  S_7
	invariant over balance : (current_layer = 0 and not exception) implies balance(state_dao) < 12
	
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		par	
			if current_layer = 0 then
				if not exception then
					let ($s = random_sender(stage)) in
						let ($r = random_receiver(stage)) in 
							let ($n = random_amount(stage)) in 
								let($f = random_function(stage)) in
									if not is_contract($s) then
										r_Transaction[$s, $r, $n, $f]
									else
										exception := true
									endif
								endlet
							endlet
						endlet
					endlet
				endif
			else
				if executing_contract(current_layer) = state_dao then
					par 
						r_Deposit[]
						r_Withdraw[]
						r_Fallback[]
					endpar
				endif
			endif
			stage := stage + 1
		endpar
			






default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in Integer) = none
	function executing_contract ($cl in Integer) = user
	function instruction_pointer ($sl in Integer) = 0
	function current_layer = 0
	function balance($c in User) = 11
	function destroyed($u in User) = false
	function payable($f in Function) = 
		switch $f
			case deposit : true
			case withdraw : false
			case none : true
			otherwise false
		endswitch
	function exception = false
	
	function stage = 0
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
	
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function customer_balance($c in User) = 0
	function state = INITIALSTATE
		

	
	
