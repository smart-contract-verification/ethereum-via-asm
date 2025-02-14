module EVMLibrarySymbolic


import ../asmeta/StandardLibrary


export *


signature:	
		
	abstract domain Function
	abstract domain User


	/* USER ATTRIBUTES */
	dynamic controlled balance : User -> Integer 
	dynamic controlled destroyed : User -> Boolean
	dynamic controlled is_contract : User -> Boolean
	
	/* METHOD ATTRIBUTE */
	dynamic controlled payable : Function -> Boolean
	
	
	/* FUNCTIONS THAT ALLOW TRANSACTIONS */
	dynamic controlled sender : Integer -> User 
	dynamic controlled amount : Integer -> Integer
	
	/* STACK MANAGEMENT */
	dynamic controlled current_layer : Integer
	
	/* ALLOW FUNCTION EXECUTIONS */
	dynamic controlled executing_function : Integer -> Function
	dynamic controlled instruction_pointer : Integer -> Integer
	dynamic controlled executing_contract : Integer -> User
	
	/* RETURN VALUES */
	dynamic controlled boolean_return : Boolean
	
	/* GENERAL MONITORED FUNCTION */
	controlled random_sender : Integer -> User
	controlled random_receiver : Integer -> User
	controlled random_function : Integer -> Function
	controlled random_amount : Integer -> Integer
	
	/* EXCEPTION */
	dynamic controlled exception : Boolean
	
	controlled stage : Integer
	
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static none : Function
	
	static user : User

	
	

	


definitions:
	
	
		

	/* 
	 * RETURN RULE
	 */
	macro rule r_Ret =
		current_layer := current_layer - 1 
		
		
	rule r_Transaction ($s in User, $r in User, $n in Integer, $f in Function) =
		if $n >= 0 and balance($s) >= $n and $s != $r and ((is_contract($r) implies (not destroyed($r)))) and ((is_contract($r) and $n > 0) implies (payable($f))) then 
			par
				seq
					balance($s) := balance($s) - $n 
					balance($r) := balance($r) + $n
				endseq
				executing_contract(current_layer + 1) := $r
				executing_function(current_layer + 1) := $f
				instruction_pointer(current_layer + 1) := 0
				sender(current_layer + 1) := $s
				amount(current_layer + 1) := $n 
				exception := false
				if is_contract($r) then
					current_layer := current_layer + 1
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
		

		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		

		



