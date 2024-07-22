module EVMlibrary


import ../asmeta/StandardLibrary


export *


signature:	
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
	
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static fallback : Function
	static none : Function
	
	static user : User
	

	


definitions:
	
	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {-3 : 30}
	domain StackLayer = {0 : 10}
	domain InstructionPointer = {0 : 5}
	domain GeneralInteger = {0 : 4}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
		
	

		
		
	/* 
	 * TRANSACTION RULE
	 */
	macro rule r_Transaction($s in User, $r in User, $n in MoneyAmount, $f in Function) =
		if balance($s) >= $n and $n >= 0 and destroyed($r)then
			let ($cl = current_layer) in
				par
					balance($s) := balance($s) - $n // subtracts the amount from the sender user balance
					balance($r) := balance($r) + $n // adds the amount to the dest user balance
					if is_contract($r) then
						par
							sender($cl + 1) := $s // set the transition attribute to the sender user
							amount($cl + 1) := $n // set the transaction attribute to the amount of coin to transfer
							current_layer := $cl + 1
							executing_contract($cl + 1) := $r
							executing_function($cl + 1) := $f
							instruction_pointer($cl + 1) := 0
						endpar
					endif
					if is_contract($s) then 
						instruction_pointer($cl) := instruction_pointer($cl) + 1
					endif
				endpar
			endlet
		endif
		
		
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
				r_Ret[]
			endif
		endlet
		
		
	macro rule r_Selfdestruct ($u in User) =
		par
			balance(executing_contract(current_layer)) := 0
			balance($u) := balance($u) + balance(executing_contract(current_layer))
			destroyed(executing_contract(current_layer)) := true
			r_Ret[]
		endpar
		

		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		

		



