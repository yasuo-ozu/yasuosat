use std::num::NonZeroI32;

pub type LitOpt = Option<NonZeroI32>;

trait VarFunctions {
	fn get(&self) -> i32;
	#[inline]
	fn polarity(&self) -> bool {
		self.get() > 0
	}
	#[inline]
	fn var(&self) -> usize {
		self.get().abs() as usize
	}
}

impl VarFunctions for NonZeroI32 {
	#[inline]
	fn get(&self) -> i32 {
		self.get()
	}
}

pub struct Solver {
	n: usize,
	clause_body: Box<[LitOpt]>,
	clause_heads: Vec<*const LitOpt>,
	assign: Vec<Option<bool>>,
	level: usize,
	pub suggest: Vec<bool>,
	levels: Vec<usize>,
	watchers: Vec<Vec<*const LitOpt>>,
}

impl Solver {
	#[inline]
	/// Create the Solver instance with clauses and number of variables.
	pub fn new(n: usize, clauses: &[Vec<i32>]) -> Option<Self> {
		if clauses
			.iter()
			.map(|clause| (clause, clause.len()))
			.all(|(clause, len)| {
				len >= 2 && clause.iter().all(|v| v != &0 && v.abs() as usize <= n)
			}) {
			// SAFETY: checked before
			unsafe { Some(Self::new_unchecked(n, clauses)) }
		} else {
			None
		}
	}

	/// Create the Solver instance with clauses and number of variables.
	///
	/// # Safety
	/// - All literals are nonzero and the absolutes of them are less than or
	/// equal to n.
	/// - The number of variables in a clause is neither 0 nor 1.
	pub unsafe fn new_unchecked(n: usize, clauses: &[Vec<i32>]) -> Self {
		let mut v_indexes = Vec::new();
		let mut v_clauses = Vec::new();
		let mut watchers = vec![Vec::new(); 2 * n + 1];
		for clause in clauses.iter() {
			// Memorize the index in v_clauses to make self.clause_heads
			v_indexes.push(v_clauses.len());
			let mut v = clause
				.iter()
				.cloned()
				// SAFETY: checked in precondition
				.map(|i| NonZeroI32::new_unchecked(i))
				.map(Some)
				.collect::<Vec<_>>();
			v_clauses.append(&mut v);
			// A clause is terminated with None in self.clause_body
			v_clauses.push(None);
		}
		// Take fat pointer
		let b = Box::into_raw(v_clauses.into_boxed_slice());
		// Take the inner address of the box using fat pointer, omitting size
		// SAFETY: fat pointer is safely converted to (pointer, usize)
		let (base_addr, _) =
			std::mem::transmute::<_, (*const Option<NonZeroI32>, usize)>(b.clone());
		let clause_heads = v_indexes
			.into_iter()
			.map(|index| base_addr.add(index))
			.collect::<Vec<_>>();
		for &clause in clause_heads.iter() {
			// SAFETY: a clause has at least two literals
			let (lit0, lit1) = (
				// use transmute() instead of unwrap() for zero-cost
				std::mem::transmute::<Option<NonZeroI32>, NonZeroI32>(*clause).get(),
				std::mem::transmute::<Option<NonZeroI32>, NonZeroI32>(*clause.add(1)).get(),
			);
			watchers[(n as i32 + lit0) as usize].push(clause);
			watchers[(n as i32 + lit1) as usize].push(clause);
		}
		Self {
			n,
			clause_body: Box::from_raw(b),
			clause_heads,
			level: 0,
			assign: vec![None; n],
			suggest: vec![false; n],
			levels: vec![0; n],
			watchers,
		}
	}

	#[inline]
	/// Check the result of proven literal.
	///
	/// # Safety
	/// lit is legal (lit.abs() <= n)
	unsafe fn eval_unchecked(&self, lit: NonZeroI32) -> Option<bool> {
		self.assign
			.get_unchecked(lit.var())
			.map(|b| b == lit.polarity())
	}

	#[inline] // make inline because it is often called from solve()
	fn propagate_once(&mut self, lit: NonZeroI32) {}
}

#[test]
fn sat_solver_struct_test() {
	let mut ss2 = Solver::new(3, vec![vec![1, -2], vec![-1, 2, 3]].as_slice()).unwrap();
	let mut ss = Solver::new(2, vec![].as_slice()).unwrap();
	std::mem::swap(&mut ss, &mut ss2); // check that copying does not break pointers
	assert_eq!(
		unsafe { *ss.clause_heads[0] },
		Some(NonZeroI32::new(1).unwrap())
	);
	assert_eq!(
		unsafe { *ss.clause_heads[1] },
		Some(NonZeroI32::new(-1).unwrap())
	);
}
