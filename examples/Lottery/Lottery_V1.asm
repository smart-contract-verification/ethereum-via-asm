asm Lottery_V1




import ../../lib/asmeta/StandardLibrary


signature:	

	





	/* --------------------------------------------LIBRARY MODEL DOMAINS-------------------------------------------- */
	
	
	
	
	abstract domain Function
	abstract domain User
	domain MoneyAmount subsetof Integer
	domain StackLayer subsetof Integer
	domain InstructionPointer subsetof Integer
	domain GeneralInteger subsetof Integer
	
	
	
	/* --------------------------------------------CONTRACT MODEL DOMANIS-------------------------------------------- */
	
	enum domain State = {INTRANSITION, INITIALSTATE}
	
	
	/* --------------------------------------------LIBRARY MODEL FUNCTIONS-------------------------------------------- */
	
	/* USER ATTRIBUTES */
	dynamic controlled balance : User -> MoneyAmount 
	dynamic controlled destroyed : User -> Boolean
	static is_contract : User -> Boolean
	
	/* METHOD ATTRIBUTE */
	dynamic controlled payable : Function -> Boolean
	
	
	/* FUNCTIONS THAT ALLOW TRANSACTIONS */
	dynamic controlled sender : StackLayer -> User 
	dynamic controlled amount : StackLayer -> MoneyAmount
	
	/* STACK MANAGEMENT */
	dynamic controlled current_layer : StackLayer
	
	/* ALLOW FUNCTION EXECUTIONS */
	dynamic controlled executing_function : StackLayer -> Function
	dynamic controlled instruction_pointer : StackLayer -> InstructionPointer
	dynamic controlled executing_contract : StackLayer -> User
	
	/* RETURN VALUES */
	dynamic controlled boolean_return : Boolean
	
	/* GENERAL MONITORED FUNCTION */
	monitored random_sender : User
	monitored random_receiver : User
	monitored random_function : Function
	monitored random_amount : MoneyAmount
	
	/* EXCEPTION */
	dynamic controlled exception : Boolean
	
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static none : Function
	
	static user : User

	
	
	
	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */


	
	dynamic controlled start : GeneralInteger
	dynamic controlled duration : GeneralInteger
	dynamic controlled fee : MoneyAmount
	
	dynamic controlled winner : User
	
	dynamic controlled picked : Boolean
	dynamic controlled prev_length : GeneralInteger
	
	dynamic controlled has_called_enter : User -> Boolean
	monitored random_winner : User
	
	dynamic controlled block_number : GeneralInteger
	
	static lottery : User
	
	static enter : Function
	static pickWinner : Function
	
	
definitions:

	/* --------------------------------------------LIBRARY MODEL-------------------------------------------- */


	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {-1 : 7}
	domain StackLayer = {0 : 2}
	domain InstructionPointer = {0 : 7}
	domain GeneralInteger = {-10 : 10}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
		

	/* 
	 * RETURN RULE
	 */
	macro rule r_Ret =
		current_layer := current_layer - 1 
		
		
	rule r_Transaction ($s in User, $r in User, $n in MoneyAmount, $f in Function) =
		if $n >= 0 and balance($s) >= $n and $s != $r and ((is_contract($r) implies (not destroyed($r)))) and ((is_contract($r) and $n > 0) implies (payable($f))) then 
			par
				seq
					balance($s) := balance($s) - $n 
					balance($r) := balance($r) + $n
				endseq
				if is_contract($r) then
					par
						sender(current_layer + 1) := $s // set the transition attribute to the sender user
						amount(current_layer + 1) := $n // set the transaction attribute to the amount of coin to transfer
						current_layer := current_layer + 1
						executing_contract(current_layer + 1) := $r
						executing_function(current_layer + 1) := $f
						instruction_pointer(current_layer + 1) := 0
						exception := false
					endpar
				endif
				if is_contract($s) then 
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endif
			endpar
		else 
			par
				if is_contract($s) then 
					r_Ret[]
				endif
				exception := true
			endpar
		endif
		

		
	/*
	 * REQUIRE RULE
	 */
	macro rule r_Require ($b in Boolean) = 
		let ($cl = current_layer) in
			if $b then
				instruction_pointer($cl) := instruction_pointer($cl) + 1
			else 
				par
					r_Ret[]
					exception := true
				endpar
			endif
		endlet
		
		
	macro rule r_Selfdestruct ($u in User) =
		if is_contract(executing_contract(current_layer)) then
			par
				balance(executing_contract(current_layer)) := 0
				balance($u) := balance($u) + balance(executing_contract(current_layer))
				destroyed(executing_contract(current_layer)) := true
				r_Ret[]
			endpar
		endif
		
	
	
	/* --------------------------------------------CONTRACT MODEL-------------------------------------------- */



	/* 
	 * ENTER FUNCTION RULE
	 */
	rule r_Enter = 
		if executing_function(current_layer) = enter then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[amount(current_layer) > 1]
				case 1 :
					par
						has_called_enter(sender(current_layer)) := true
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 2 : 
					r_Ret[]
			endswitch
		endif
		
	rule r_PickWinner =
		if executing_function(current_layer) = pickWinner then
			switch instruction_pointer(current_layer)
				case 0 :
					r_Require[block_number >= start + duration]
				case 1 : 
					par
						if has_called_enter(random_winner) then
							winner := random_winner
						else
							r_Require[false]
						endif
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 2 : 
					par
						forall $u in User with true do
							has_called_enter($u) := false
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 3 : 
					par
						fee := 1
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 4 : 
					par
						start := block_number
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 5 : 
					r_Transaction[lottery, sender(current_layer), fee, none]
				case 6 : 
					r_Transaction[lottery, winner, balance(lottery), none]
				case 7 : 
					r_Ret[]
			endswitch
		endif






	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		if executing_function(current_layer) != enter and  executing_function(current_layer) != pickWinner then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */









	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		if current_layer = 0 then
			if not exception then
				let ($r = random_receiver, $n = random_amount, $f = random_function) in
					par
						r_Transaction[user, $r, $n, $f]
						block_number := block_number + 1
					endpar
				endlet
			endif
		else
			if executing_contract(current_layer) = lottery then
				par 
					r_Enter[]
					r_PickWinner[]
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
	function balance($c in User) = 3
	function destroyed($u in User) = false
	function payable($f in Function) = 
		switch $f
			case enter : true
			case pickWinner : false
			otherwise false
		endswitch
	function exception = false
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */

 	function block_number = 0
 	function start = 0
 	
 	function duration = 5
		

	
	
