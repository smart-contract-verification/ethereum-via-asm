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
	dynamic controlled destroyed : Prod(User, StackLayer) -> Boolean
	static is_contract : User -> Boolean

	
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
	dynamic controlled payable : Function -> Boolean
	
    /* GENERAL MONITORED FUNCTION */
    /* For symbolic execution, changed to: 'controlled ... : Integer -> ...', where the integer is the 'stage' of the run */
    controlled random_user : Integer -> User
    controlled random_function : Integer -> Function
    controlled random_amount : Integer -> MoneyAmount

    // 'stage' of the sequential run
    controlled stage : Integer
	
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
	 * TRANSACTION RULE
	 */
	macro rule r_Transaction_Env =
		par
			if balance(sender(current_layer), global_state_layer) >= amount(current_layer) and amount(current_layer) >= 0 then
				let ($cl = current_layer) in
					par
                        seq             // use seq to avoid inconsistent updates when user is the same
                            balance(sender($cl), global_state_layer) := balance(sender($cl), global_state_layer) - amount($cl) // subtracts the amount from the sender user balance
                            balance(receiver($cl), global_state_layer) := balance(receiver($cl), global_state_layer) + amount($cl) // adds the amount to the dest user balance
                        endseq
						if is_contract(receiver($cl)) then
							par
								if amount($cl) > 0 and not payable(function_call($cl)) then
									r_Throw[]
								endif
								executing_contract($cl) := receiver($cl)
								executing_function($cl) := function_call($cl)
								instruction_pointer($cl) := 0
							endpar
						endif
						if is_contract(sender($cl)) then 
							instruction_pointer($cl - 1) := instruction_pointer($cl - 1) + 1
						endif
					endpar
				endlet
			else 
				r_Throw[]
			endif
			transaction := false
			
		endpar
		
	macro rule r_Transaction($s in User, $r in User, $n in MoneyAmount, $f in Function) = 
		par
			transaction := true
			sender(current_layer + 1) := $s
			receiver(current_layer + 1) := $r 
			amount(current_layer + 1) := $n
			function_call(current_layer + 1) := $f
			call_response(current_layer + 1) := true
			current_layer := current_layer + 1
			
			r_Save_Env[global_state_layer + 1]
			global_state_layer := global_state_layer + 1
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
		
	macro rule r_Selfdestruct ($u in User) = 
		if is_contract($u) then
			par
				balance($u, global_state_layer) := balance($u, global_state_layer) + balance(executing_contract(current_layer), global_state_layer)
				balance(executing_contract(current_layer), global_state_layer) := 0
				destroyed(executing_contract(current_layer), global_state_layer) := true
				r_Ret[]
			endpar
		endif
