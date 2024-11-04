asm StateBasedDAOflattened




import ../../lib/asmeta/CTLlibrary
import ../../lib/asmeta/StandardLibrary
//import ../../lib/attackers/SelfdestructAttacker
//import ../../lib/solidity/EVMlibrary



signature:	

	





	enum domain State = {INTRANSITION, INITIALSTATE}
	
	
	
	abstract domain Function
	abstract domain User
	domain MoneyAmount subsetof Integer
	domain StackLayer subsetof Integer
	domain InstructionPointer subsetof Integer
	domain GeneralInteger subsetof Integer
	
	/* USER ATTRIBUTES */
	dynamic controlled balance : User -> MoneyAmount 
	dynamic controlled destroyed : User -> Boolean
	derived is_contract : User -> Boolean
	
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
	monitored random_user : User
	monitored random_function : Function
	monitored random_amount : MoneyAmount
	
	/* EXCEPTION */
	dynamic controlled exception :Boolean
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static none : Function
	
	static user : User
	
	
	
	
	
	
	controlled input_user : User
	
	static attacker : User
	
	static attack : Function
	
	
	
	
	

	/* CONTRACT ATTRIBUTES */
	dynamic controlled customer_balance : User -> MoneyAmount 
	
	dynamic controlled state : State
	
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static state_dao : User
	
	static deposit : Function
	static withdraw : Function 
	
	


	
	
definitions:


	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {0 : 4}
	domain StackLayer = {0 : 2}
	domain InstructionPointer = {0 : 7}
	domain GeneralInteger = {0 : 0}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
		

	rule r_Transaction ($s in User, $r in User, $n in MoneyAmount, $f in Function) =
		par
			if balance($s) >= 0 then 
				par
					balance($s) := balance($s) - $n 
					balance($r) := balance($r) + $n
				endpar
			else 
				exception := true
			endif
		
			
			if is_contract($r) then
				par
					sender(current_layer + 1) := $s // set the transition attribute to the sender user
					amount(current_layer + 1) := $n // set the transaction attribute to the amount of coin to transfer
					current_layer := current_layer + 1
					executing_contract(current_layer + 1) := $r
					executing_function(current_layer + 1) := $f
					instruction_pointer(current_layer + 1) := 0
				endpar
			endif
			
			if is_contract($s) then 
				instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
			endif
			
			
			if destroyed($r) then 
				exception := true
			endif
			
			
			if is_contract($r) and $n > 0 and not payable($f) then
				exception := true
			endif
		endpar
		
	/* 
	 * RETURN RULE
	 */
	macro rule r_Ret =
		current_layer := current_layer - 1 
		
	/*
	 * REQUIRE RULE
	 */
	macro rule r_Require ($b in Boolean) = 
		let ($cl = current_layer) in
			if $b then
				instruction_pointer($cl) := instruction_pointer($cl) + 1
			else 
				
				exception := true
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
		
		
		
		
	/* --------------------------------------------ATTACKER CONTRACT-------------------------------------------- */
		
		
		
	rule r_Attack =
		if executing_function(current_layer) = attack then
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						input_user := random_user
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 : 
					r_Selfdestruct[input_user]
			endswitch
		endif
	


	rule r_Fallback_attacker = 
			if executing_function(current_layer) != attack then
				switch instruction_pointer(current_layer)
					case 0 : 
						r_Require[false]
				endswitch
			endif



	
	
	
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
					r_Require[balance(executing_contract(current_layer)) < 2]
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
	invariant over exception : exception = false
	
	invariant over state : current_layer = 0 implies state = INITIALSTATE
	
	
	/*
	 * CTLSPEC
	 */
	CTLSPEC ag((balance(state_dao) >= 2 and exception = false)implies ef(balance(state_dao) < 2 and exception = false))
	CTLSPEC ag((state = INTRANSITION and exception = false) implies ef(state = INITIALSTATE and exception = false))

		
	
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
				endpar
			else 
				par
					r_Attack[]
					r_Fallback_attacker[]
				endpar
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
	function balance($c in User) = 1
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
		

	
	
