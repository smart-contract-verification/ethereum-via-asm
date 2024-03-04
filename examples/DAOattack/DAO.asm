asm DAO




import ../../Libraries/CTLlibrary
import ../../SolidityLibraries/SimpleReentrancyAttack
import ../../SolidityLibraries/EVMlibrary
import ../../Libraries/StandardLibrary


signature:	

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
	
	
	
	/* --------------------------------------------BANK CONTRACT IMPLEMENTATION-------------------------------------------- */

	/* 
	 * DEPOSIT FUNCTION RULE
	 */
	 
	rule r_Deposit_bank1 =
		let ($cl = current_layer) in
			let ($scl = sender($cl)) in
				if executing_function($cl) = deposit then 
					switch instruction_pointer($cl)
						case 0 : 
							par
								value_deposit($cl) := amount($cl)
								instruction_pointer($cl) := instruction_pointer($cl) + 1
							endpar
						case 1 : 
							par 
								customer_balance($scl) := customer_balance($scl) + value_deposit($cl)
								r_Ret[] 
							endpar
					endswitch
				endif
			endlet
		endlet
		
		
	/* 
	 * WITHDARW FUNCTION RULE
	 */
	 
	rule r_Withdraw_bank1 = 
		let ($cl = current_layer) in
			let ($scl = sender($cl)) in
				if executing_function($cl) = withdraw then
					switch instruction_pointer($cl)
						case 0 : 
							par
								value_withdraw($cl) := 1
								instruction_pointer($cl) := instruction_pointer($cl) + 1
							endpar
						case 1 : 
							if customer_balance($scl) >= value_withdraw($cl) then
								r_Transaction[dao, $scl, value_withdraw($cl), fallback]	
							else
								r_Ret[]
							endif
						case 2 : 
							par
								customer_balance($scl) := customer_balance($scl) - value_withdraw($cl)
								r_Ret[]
							endpar
					endswitch
				endif
			endlet
		endlet
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	 
	rule r_Fallback_bank1 =
		let ($cl = current_layer) in
			if executing_function($cl) != deposit and  executing_function($cl) != withdraw then 
				switch instruction_pointer($cl)
					case 0 : 
						 r_Ret[]
				endswitch
			endif
		endlet	
		
		
	/* --------------------------------------------MAINS AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */
	 
	 invariant over customer_balance : customer_balance(attacker) >= 0
	
	
	/*
	 * CTLSPEC
	 */
	CTLSPEC ef(customer_balance(attacker) < 0)

		
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 	
		if not is_contract(executing_contract(current_layer)) then
			r_Transaction[user, random_user, 1, random_function]
		else
			if executing_contract(current_layer) = dao then
				par 
					r_Deposit_bank1[]
					r_Withdraw_bank1[]
					r_Fallback_bank1[]
				endpar
			else 
				r_Attacker[]
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
	function balance($c in User) = 10
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function customer_balance($c in User) = 1
		

	
	
