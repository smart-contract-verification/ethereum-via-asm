asm KotetFlattenedSymbolic_V1




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrarySymbolic


signature:	
	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled king : User
	dynamic controlled claim_price : Integer
	
	dynamic controlled old_king : User
	dynamic controlled old_claim_price  : Integer
	
	static kotET : User
	static initial_king : User
	
	


	
	
definitions:
	
	
	/* --------------------------------------------CONTRACT MODEL-------------------------------------------- */
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		switch instruction_pointer(current_layer) 
			case 0: 
				r_Require[amount(current_layer) >= claim_price]
			case 1: 
				r_Transaction[kotET, king, claim_price + 2, none]
			case 2: 
				par
					king := sender(current_layer)
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endpar
			case 3:
				par
					claim_price := claim_price + 1
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endpar
			case 4 : 
				r_Ret[]
		endswitch
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT - S_30
	 */
	 
	 // ogni volta che un utente diventa king deve essere un utente diverso dal king precedente - S_7
	 invariant over king : (current_layer = 0 and not exception and executing_contract(1) = kotET) implies (old_king != king)
	 
	 // non è possibile che il balance del contratto arrivi a 0 - ~ S_0
	 invariant over balance : (not exception) implies balance(kotET) > 0
	 	 
	 // claim price non può essere maggiore di tutti i balance degli utenti - ~ S_0
	 invariant over claim_price : not (forall $u in User with balance($u) < claim_price )
	 
	 // se viene fatta una chiamata alla fallback di Kotet con un amount maggiore o uguale a claim_price non viene sollevata un eccezione - S_3
	 invariant over king : (current_layer = 0 and executing_contract(1) = kotET and amount(1) >= old_claim_price) implies (not exception)




	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		par
			if current_layer = 0 then
				if not exception then
					let ($r = random_receiver(stage)) in
						let ($n = random_amount(stage)) in 
							let ($f = random_function(stage)) in
								par
									r_Transaction[user, $r, $n, $f]
									old_king := king
									old_claim_price := claim_price
								endpar
							endlet
						endlet
					endlet
				endif
			else
				if executing_contract(current_layer) = kotET then
					r_Fallback[]
				endif
			endif
			stage := stage + 1
		endpar
			






default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in Integer) = none
	function executing_contract ($cl in Integer) = user
	function instruction_pointer ($sl in Integer) = 0
	function current_layer = 0
	//function balance($c in User) = 3
	function destroyed($u in User) = false
	function payable($f in Function) = true
	function exception = false
	
	function stage = 0
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			case initial_king : false
			otherwise true
		endswitch
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	 
	function king = initial_king 
	function claim_price = 1
		

	
	
