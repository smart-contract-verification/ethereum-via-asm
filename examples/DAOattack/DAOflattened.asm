asm DAOflattened



import ../../lib/asmeta/CTLlibrary
import ../../lib/asmeta/StandardLibrary



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

	
	
	
	
	
	
	
		
	static attacker : User
	
	static attack : Function
	

	/* CONTRACT ATTRIBUTES */
	dynamic controlled customer_balance : User -> MoneyAmount 
	
	
	/* FUNCTIONS PARAMETERS */
	dynamic controlled value_deposit : StackLayer -> MoneyAmount 
	dynamic controlled value_withdraw : StackLayer -> MoneyAmount 
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static dao : User
	
	static deposit : Function
	static withdraw : Function 
	
	
	
	
	


	
	
definitions:





		
	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {-3 : 10}
	domain StackLayer = {0 : 6}
	domain InstructionPointer = {0 : 5}
	domain GeneralInteger = {0 : 4}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch	
		
		
		
	rule r_Attack =
		let ($cl=current_layer) in
			if executing_function($cl) = attack then
				switch instruction_pointer($cl)
					case 0 : 
						par
							if balance(attacker) >= 0 then 
								par
									balance(attacker) := balance(attacker) - 0 
									balance(random_user) := balance(random_user) + 0 
								endpar
							else 
								skip
							endif
							if destroyed(random_user) then 
								skip
							endif
							if is_contract(random_user) and 0 > 0 and not payable(random_function) then
								skip
							endif
							if is_contract(random_user) then
								par
									sender($cl + 1) := attacker // set the transition attribute to the sender user
									amount($cl + 1) := 0 // set the transaction attribute to the amount of coin to transfer
									current_layer := current_layer + 1
									executing_contract($cl + 1) := random_user
									executing_function($cl + 1) := random_function
									instruction_pointer($cl + 1) := 0
								endpar
							endif
							if is_contract(attacker) then 
								instruction_pointer($cl) := instruction_pointer($cl) + 1
							endif
						endpar
					case 1 : 
						current_layer := current_layer - 1  
				endswitch
			endif
		endlet



	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	rule r_Fallback_attacker = 
		let ($cl=current_layer) in
			if executing_function($cl) != attack then
				switch instruction_pointer($cl)
					case 0 : 
						par
							if balance(attacker) >= 0 then 
								par
									balance(attacker) := balance(attacker) - 0 
									balance(sender($cl)) := balance(sender($cl)) + 0 
								endpar
							else 
								skip
							endif
							if destroyed(sender($cl)) then 
								skip
							endif
							if is_contract(sender($cl)) and 0 > 0 and not payable(random_function) then
								skip
							endif
							if is_contract(sender($cl)) then
								par
									sender($cl + 1) := attacker // set the transition attribute to the sender user
									amount($cl + 1) := 0 // set the transaction attribute to the amount of coin to transfer
									current_layer := current_layer + 1
									executing_contract($cl + 1) := sender($cl)
									executing_function($cl + 1) := random_function
									instruction_pointer($cl + 1) := 0
								endpar
							endif
							if is_contract(attacker) then 
								instruction_pointer($cl) := instruction_pointer($cl) + 1
							endif
						endpar
					case 1 :
						par
							boolean_return := true
							current_layer := current_layer - 1  
						endpar
				endswitch
			endif
		endlet

		
		
	
		
		
	
	
	
	/* --------------------------------------------BANK CONTRACT IMPLEMENTATION-------------------------------------------- */

	/* 
	 * DEPOSIT FUNCTION RULE
	 */
	 
	rule r_Deposit_bank1 =
		let ($cl=current_layer) in
			if executing_function($cl) = deposit then 
				par
					if instruction_pointer($cl) = 0 then 
						par
							value_deposit($cl) := amount($cl)
							instruction_pointer($cl) := instruction_pointer($cl) + 1
						endpar
					endif
					if instruction_pointer($cl) = 1 then 
						par 
							customer_balance(sender($cl)) := customer_balance(sender($cl)) + value_deposit($cl)
							current_layer := current_layer - 1 
						endpar
					endif
				endpar
			endif
		endlet
		
		
	/* 
	 * WITHDARW FUNCTION RULE
	 */
	 
	rule r_Withdraw_bank1 = 
		let ($cl=current_layer) in
			if executing_function($cl) = withdraw then
			 
				par
					if instruction_pointer($cl) = 0 then 
						par
							value_withdraw($cl) := 1
							instruction_pointer($cl) := instruction_pointer($cl) + 1
						endpar
					endif
					if instruction_pointer($cl) = 1 then 
						if customer_balance(sender($cl)) >= value_withdraw($cl) then
							par
								if balance(dao) >= value_withdraw($cl) then 
									par
										balance(dao) := balance(dao) - value_withdraw($cl) 
										balance(sender($cl)) := balance(sender($cl)) + value_withdraw($cl) 
									endpar
								else 
									skip
								endif
								if destroyed(sender($cl)) then 
									skip
								endif
								if is_contract(sender($cl)) and value_withdraw($cl) > 0 and not payable(none) then
									skip
								endif
								if is_contract(sender($cl)) then
									par
										sender($cl + 1) := dao // set the transition attribute to the sender user
										amount($cl + 1) := value_withdraw($cl) // set the transaction attribute to the amount of coin to transfer
										current_layer := current_layer + 1
										executing_contract($cl + 1) := sender($cl)
										executing_function($cl + 1) := none
										instruction_pointer($cl + 1) := 0
									endpar
								endif
								if is_contract(dao) then 
									instruction_pointer($cl) := instruction_pointer($cl) + 1
								endif
							endpar
						else
							current_layer := current_layer - 1  
						endif
					endif
					if instruction_pointer($cl) = 2 then 
						par
							customer_balance(sender($cl)) := customer_balance(sender($cl)) - value_withdraw($cl)
							current_layer := current_layer - 1  
						endpar
					endif
				endpar
			endif
		endlet
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	 
	rule r_Fallback_bank1 =
		let ($cl=current_layer) in
			if executing_function($cl) != deposit and  executing_function($cl) != withdraw then 
				if instruction_pointer($cl) = 0 then  
					 current_layer := current_layer - 1  
				endif
			endif
		endlet
		
		
	/* --------------------------------------------MAINS AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */
	 
	 //invariant over customer_balance : customer_balance(attacker) >= 0
	 //invariant over exception : exception = false
	
	
	/*
	 * CTLSPEC
	 */
	CTLSPEC ef(customer_balance(attacker) < 0)

		
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 	
		let ($cl=current_layer) in
			if $cl = 0 then
				par
					if balance(user) >= random_amount then 
						par
							balance(user) := balance(user) - random_amount 
							balance(random_user) := balance(random_user) + random_amount 
						endpar
					else 
						skip
					endif
					if destroyed(random_user) then 
						skip
					endif
					if is_contract(random_user) and random_amount > 0 and not payable(random_function) then
						skip
					endif
					if is_contract(random_user) then
						par
							sender($cl + 1) := user // set the transition attribute to the sender user
							amount($cl + 1) := random_amount // set the transaction attribute to the amount of coin to transfer
							current_layer := current_layer + 1
							executing_contract($cl + 1) := random_user
							executing_function($cl + 1) := random_function
							instruction_pointer($cl + 1) := 0
						endpar
					endif
					if is_contract(user) then 
						instruction_pointer($cl) := instruction_pointer($cl) + 1
					endif
				endpar			
			else
				
				if executing_contract($cl) = dao then
					par 
						r_Deposit_bank1[]
						r_Withdraw_bank1[]
						r_Fallback_bank1[]
					endpar
				else 
					par
						r_Attack[]
						r_Fallback_attacker[]
					endpar
				endif
			endif
		endlet

			






default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = if $sl = 0 then none endif 
	function executing_contract ($cl in StackLayer) = if $cl = 0 then user endif
	function instruction_pointer ($sl in StackLayer) = if $sl = 0 then 0 endif
	function current_layer = 0
	function balance($c in User) = 3
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
	function customer_balance($c in User) = 1
		

	
	
