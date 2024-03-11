asm DAO




import ../../lib/asmeta/CTLlibrary
import ../../lib/asmeta/StandardLibrary
import ../../lib/attackers/SimpleReentrancyAttack
import ../../lib/solidity/EVMlibrary



signature:	

	/* CONTRACT ATTRIBUTES */
	dynamic controlled customer_balance : Prod(User, StackLayer) -> MoneyAmount 
	
	
	/* FUNCTIONS PARAMETERS */
	dynamic controlled value_deposit : StackLayer -> MoneyAmount 
	dynamic controlled value_withdraw : StackLayer -> MoneyAmount 
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static dao : User
	
	static deposit : Function
	static withdraw : Function 
	
	


	
	
definitions:
	
	
	
	/* --------------------------------------------BANK CONTRACT IMPLEMENTATION-------------------------------------------- */

	rule r_Save ($n in StackLayer) =
		forall $u in User with true do 
			customer_balance($u, $n) := customer_balance($u, global_state_layer)


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
								customer_balance($scl, global_state_layer) := customer_balance($scl, global_state_layer) + value_deposit($cl)
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
							if customer_balance($scl, global_state_layer) >= value_withdraw($cl) then
								r_Transaction[dao, $scl, value_withdraw($cl), fallback]	
							else
								r_Ret[]
							endif
						case 2 : 
							par
								customer_balance($scl, global_state_layer) := customer_balance($scl, global_state_layer) - value_withdraw($cl)
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
	 
	 invariant over customer_balance : customer_balance(attacker, global_state_layer) >= 0
	
	
	/*
	 * CTLSPEC
	 */
	CTLSPEC ef(customer_balance(attacker, global_state_layer) < 0)

		
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 	
		if transaction then 
				seq
					r_Save[global_state_layer + 1]
					r_Save_Env[global_state_layer + 1]
					r_Save_Att[global_state_layer + 1]
					global_state_layer := global_state_layer + 1
					r_Transaction_Env[]
				endseq
		else
			if current_layer = 0 then
				seq
					par 
						r_Save[0]
						r_Save_Env[0]
						global_state_layer := 0
					endpar
					r_Transaction[user, random_user, 1, random_function]
					
				endseq
			else
				switch executing_contract(current_layer) 
					case dao : 
						par 
							r_Deposit_bank1[]
							r_Withdraw_bank1[]
							r_Fallback_bank1[]
						endpar
					case attacker :
						r_Attacker[]
					otherwise 
						r_Ret[]
				endswitch
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
	function transaction = false
	function balance($c in User, $n in StackLayer) = if $n = 0 then 10 endif
	function global_state_layer = 0
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function customer_balance($c in User, $n in StackLayer) = if $n = 0 then 1 endif
		

	
	
