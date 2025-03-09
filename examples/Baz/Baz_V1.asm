asm Baz_V1




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrary


signature:	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled state1 : Boolean
	dynamic controlled state2 : Boolean
	dynamic controlled state3 : Boolean
	dynamic controlled state4 : Boolean
	dynamic controlled state5 : Boolean
	
	monitored a_mon : GeneralInteger
	monitored b_mon : GeneralInteger
	monitored c_mon : GeneralInteger
	
	controlled a : GeneralInteger
	controlled b : GeneralInteger
	controlled c : GeneralInteger
	
	controlled d : GeneralInteger


	/* USER and METHODS */
	static u_baz : User
	
	static f_baz : Function
	
	


	
	
definitions:

	
	/* --------------------------------------------CONTRACT MODEL-------------------------------------------- */

	/* 
	 * DESTROY FUNCTION RULE
	 */
		
	
	/* 
	 * BAZ FUNCTION RULE
	 */
	rule r_Baz = 
		if executing_function(current_layer) = f_baz then 
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						a := a_mon
						b := b_mon
						c := c_mon
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 :
					par
						d := b + c
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 2 : 
					if d < 1 then 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					else
						instruction_pointer(current_layer) := 6
					endif
				case 3 : 
					if b < 3 then
						par
							state1 := true
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 4 : 
					if a = 42 then
						par
							state2 := true
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 5 : 
					par
						state3 := true
						r_Ret[]
					endpar
				case 6 : 
					if c < 42 then
						par
							state4 := true
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 7 : 
					par
						state5 := true
						r_Ret[]
					endpar
			endswitch
		endif
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		if executing_function(current_layer) != f_baz then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT S_30
	 */
	 
	 // not all states are true -  S_29
	 invariant over state1, state2, state3, state4, state5 : ((not state1) or (not state2) or (not state3) or (not state4) or (not state5))

	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		if current_layer = 0 then
			if not exception then
				let ($r = random_receiver) in
					let ($n = random_amount) in 
						let ($f = random_function) in
							r_Transaction[user, $r, $n, $f]
						endlet
					endlet
				endlet
			endif
		else
			if executing_contract(current_layer) = u_baz then
				par 
					r_Baz[]
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
			case f_baz : false
			otherwise false
		endswitch
	function exception = false
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function state1 = false
	function state2 = false
	function state3 = false
	function state4 = false
	function state5 = false
	
		

	
	
