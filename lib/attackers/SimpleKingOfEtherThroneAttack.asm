module SimpleKingOfEtherThroneAttack


import ../solidity/EVMlibrary
import ../asmeta/StandardLibrary


export *


signature:

	controlled input_user : Integer ->  User
	
	static attacker : User
	
	static attack : Function
	static destroy : Function


definitions:


	rule r_Save_Att ($n in StackLayer) = 
		skip
		
		
	rule r_Destroy =
		if executing_function(current_layer) = destroy then
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						input_user(current_layer) := random_user(stage)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 : 
					r_Selfdestruct[input_user(current_layer)]
			endswitch
		endif
	

	rule r_Call =
		let ($cl = current_layer) in
			let ($scl = sender($cl)) in
				if executing_function($cl) = attack then
					switch instruction_pointer($cl)
						case 0 : 
							r_Transaction[attacker, random_user(stage), random_amount(stage), random_function(stage)]
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
						r_Throw[]
					case 1 :
						r_Ret[]
				endswitch
			endif
		endlet
		
		
	
	rule r_Attacker =  
		par
			r_Destroy[]
			r_Call[]
			r_Fallback_attacker[]
		endpar


