module SimpleReentrancyAttack


import ../solidity/EVMlibrary
import ../asmeta/StandardLibrary


export *


signature:
	
	static attacker : User
	
	static attack : Function


definitions:

	rule r_Attack =
		let ($cl = current_layer) in
			let ($scl = sender($cl)) in
				if executing_function($cl) = attack then
					switch instruction_pointer($cl)
						case 0 : 
							r_Transaction[attacker, random_user, 0, random_function]
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
						r_Transaction[attacker, sender($cl), 0, random_function]
					case 1 :
						par
							boolean_return := true
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


