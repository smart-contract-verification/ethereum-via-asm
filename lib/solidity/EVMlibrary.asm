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
	dynamic controlled balance : Prod(User, StackLayer) -> MoneyAmount 
	derived is_contract : User -> Boolean
	
	/* FUNCTIONS THAT ALLOW TRANSACTIONS */
	dynamic controlled transaction : Boolean
	dynamic controlled sender : StackLayer -> User 
	dynamic controlled receiver : StackLayer -> User
	dynamic controlled amount : StackLayer -> MoneyAmount
	dynamic controlled function_call : StackLayer -> Function
	
	/* STACK MANAGEMENT */
	dynamic controlled current_layer : StackLayer
	
	/* ALLOW FUNCTION EXECUTIONS */
	dynamic controlled executing_function : StackLayer -> Function
	dynamic controlled instruction_pointer : StackLayer -> InstructionPointer
	dynamic controlled executing_contract : StackLayer -> User
	
	/* GENERAL MONITORED FUNCTION */
	monitored random_user : User
	monitored random_function : Function
	monitored random_amount : MoneyAmount
	
	/* EXCEPTION HANDLING */
	dynamic controlled global_state_layer : StackLayer
	dynamic controlled call_response : StackLayer -> Boolean
	
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static fallback : Function
	static none : Function
	
	static user : User
	

	


definitions:
	
	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {-3 : 30}
	domain StackLayer = {0 : 10}
	domain InstructionPointer = {0 : 10}
	domain GeneralInteger = {0 : 4}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
		
	



	macro rule r_Save_Env ($n in StackLayer) =
		forall $u in User with true do 
			balance($u, $n) := balance($u, global_state_layer)
		
		
	/* 
	 * TRANSACTION RULE
	 */
	macro rule r_Transaction_Env =
		par
			if balance(sender(current_layer + 1), global_state_layer) >= amount(current_layer + 1) and amount(current_layer + 1) >= 0 then
				let ($cl = current_layer) in
					par
						balance(sender($cl + 1), global_state_layer) := balance(sender($cl + 1), global_state_layer) - amount($cl + 1) // subtracts the amount from the sender user balance
						balance(receiver($cl + 1), global_state_layer) := balance(receiver($cl + 1), global_state_layer) + amount($cl + 1) // adds the amount to the dest user balance
						if is_contract(receiver($cl + 1)) then
							par
								current_layer := $cl + 1
								executing_contract($cl + 1) := receiver($cl + 1)
								executing_function($cl + 1) := function_call($cl + 1)
								instruction_pointer($cl + 1) := 0
							endpar
						endif
						if is_contract(sender($cl + 1)) then 
							instruction_pointer($cl) := instruction_pointer($cl) + 1
						endif
					endpar
				endlet
			endif
			transaction := false
			call_response(current_layer + 1) := true
		endpar
		
	macro rule r_Transaction($s in User, $r in User, $n in MoneyAmount, $f in Function) = 
		par
			transaction := true
			sender(current_layer + 1) := $s
			receiver(current_layer + 1) := $r 
			amount(current_layer + 1) := $n
			function_call(current_layer + 1) := $f
		endpar
		
		
	/* 
	 * RETURN RULE
	 */
	macro rule r_Ret =
		current_layer := current_layer - 1 
		
	macro rule r_Throw =
		par
			global_state_layer := global_state_layer - 1
			call_response(current_layer) := false
			r_Ret[]
		endpar
		
	/*
	 * REQUIRE RULE
	 */
	macro rule r_Require ($b in Boolean) = 
		let ($cl = current_layer) in
			if $b then
				instruction_pointer($cl) := instruction_pointer($cl) + 1
			else 
				r_Throw[]
			endif
		endlet
		

		
		
		

	
		
		
		

		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		

		



