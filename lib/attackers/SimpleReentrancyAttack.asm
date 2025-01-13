module SimpleReentrancyAttack


import ../solidity/EVMlibrary
import ../asmeta/StandardLibrary


export *


signature:

	
	dynamic controlled boolean_return : StackLayer -> Boolean

	
	static attacker : User
	
	static attack : Function


definitions:

	rule r_Save_Att ($n in StackLayer) =
		boolean_return($n) := boolean_return(global_state_layer)

	rule r_Attack =
		let ($cl = current_layer) in
			let ($scl = sender($cl)) in
				if executing_function($cl) = attack then
					switch instruction_pointer($cl)
						case 0 : 
							r_Transaction[attacker, random_user (stage), 0, random_function (stage)]
						case 1 : 
							r_Ret[]
					endswitch
				endif
			endlet
		endlet
	


	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	rule r_Fallback_attacker = 
		let ($cl = current_layer) in
			if executing_function($cl) != attack then
				switch instruction_pointer($cl)
					case 0 : 
						r_Transaction[attacker, sender($cl), 0, random_function (stage)]
					case 1 :
						par
							boolean_return(global_state_layer) := true
							r_Ret[]
						endpar
				endswitch
			endif
		endlet
		
		
	
	rule r_Attacker =  
		par
			r_Attack[]
			r_Fallback_attacker[]
		endpar


