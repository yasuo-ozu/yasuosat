use std::num::NonZeroI32;

// NonZeroI32 is non-zero, so the pointer is valid (non-null)
pub type ClausePtr = (*mut NonZeroI32, *mut NonZeroI32);

trait LitFunctions {
	fn as_i32(&self) -> i32;
	#[inline]
	fn as_bool(&self) -> bool {
		self.as_i32() > 0
	}
	#[inline]
	fn var(&self) -> usize {
		self.as_i32().abs() as usize
	}
	#[inline]
	// TODO: reduce casting cost
	fn get_loc(&self, n: usize) -> usize {
		(n as i32 + self.as_i32()) as usize
	}
	fn negative(&self) -> Self;
}

impl LitFunctions for NonZeroI32 {
	#[inline]
	fn as_i32(&self) -> i32 {
		self.get()
	}
	#[inline]
	fn negative(&self) -> Self {
		unsafe { NonZeroI32::new_unchecked(-self.get()) }
	}
}

pub struct Solver {
	n: usize,
	clause_body: Box<[NonZeroI32]>,
	clauses: Vec<ClausePtr>,
	assign: Vec<Option<bool>>,
	level: usize,
	pub suggest: Vec<bool>,
	levels: Vec<usize>,
	watchers: Vec<Vec<ClausePtr>>,
}

enum PropagateResult {
	Ok(Vec<(NonZeroI32, Option<ClausePtr>)>),
	Conflict(ClausePtr),
}

impl Solver {
	#[inline]
	/// Create the Solver instance with clauses and number of variables.
	pub fn new(n: usize, clauses: &[Vec<i32>]) -> Option<Self> {
		if clauses
			.iter()
			.map(|clause| (clause, clause.len()))
			.all(|(clause, len)| {
				len >= 2 && clause.iter().all(|v| v != &0 && v.abs() as usize <= n) && {
					let mut v = clause.iter().cloned().map(i32::abs).collect::<Vec<_>>();
					v.sort_unstable();
					v.windows(2)
						.all(|s| unsafe { s.get_unchecked(0) != s.get_unchecked(1) })
				}
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
	/// - The numbers in a clause is not duplicated.
	pub unsafe fn new_unchecked(n: usize, clauses: &[Vec<i32>]) -> Self {
		let mut v_indexes = Vec::new();
		let mut v_clauses = Vec::new();
		let mut watchers = vec![Vec::new(); 2 * n + 1];
		for clause in clauses.iter() {
			// Memorize the index in v_clauses to make self.clause_heads
			v_indexes.push(v_clauses.len());
			debug_assert!(clause.len() >= 2);
			let mut v = clause
				.iter()
				.cloned()
				// SAFETY: checked in precondition
				.map(|i| NonZeroI32::new_unchecked(i))
				.collect::<Vec<_>>();
			v_clauses.append(&mut v);
		}
		v_indexes.push(v_clauses.len());
		// Take fat pointer
		let b = Box::into_raw(v_clauses.into_boxed_slice());
		// Take the inner address of the box using fat pointer, omitting size
		// SAFETY: fat pointer is safely converted to (pointer, usize)
		let (base_addr, _) = std::mem::transmute::<_, (*mut NonZeroI32, usize)>(b.clone());
		let clauses = v_indexes
			.windows(2)
			.map(|win| (base_addr.add(win[0]), base_addr.add(win[1] - 1)))
			.collect::<Vec<_>>();
		for clause in clauses.iter() {
			watchers[(*clause.0).negative().get_loc(n)].push(*clause);
			watchers[(*clause.1).negative().get_loc(n)].push(*clause);
		}
		Self {
			n,
			clause_body: Box::from_raw(b),
			clauses,
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
			.map(|b| b == lit.as_bool())
	}

	#[inline] // make inline because it is often called from solve()
	fn propagate_once(&mut self, lit: NonZeroI32) -> PropagateResult {
		assert!(lit.var() <= self.n);
		let mut i = 0;
		let mut later_assigns = Vec::new();
		'outer: loop {
			let clause = if let Some(c) =
				unsafe { self.watchers.get_unchecked_mut(lit.get_loc(self.n)) }.get_mut(i)
			{
				*c
			} else {
				break;
			};

			if unsafe { *clause.1 } == lit.negative() {
				// make sure that clause.0 is false
				unsafe {
					std::ptr::swap(clause.0, clause.1);
				}
			}
			debug_assert!(unsafe { *clause.0 }.negative() == lit);

			if unsafe { self.eval_unchecked(*clause.1) } == Some(true) {
				// already satisfied (the clause is already dropped in this stage)
				i += 1;
				continue;
			}

			{
				// search literal which is not false (true or unassigned)
				let mut p = unsafe { clause.0.add(1) };
				while p < clause.1 {
					if unsafe { self.eval_unchecked(*p) } != Some(false) {
						unsafe {
							std::ptr::swap(p, clause.1);
						}
						unsafe { self.watchers.get_unchecked_mut(lit.get_loc(self.n)) }
							.swap_remove(i);
						unsafe { self.watchers.get_unchecked_mut((*p).get_loc(self.n)) }
							.push(clause);
						// do not increase i here
						continue 'outer;
					}
					unsafe {
						p = p.add(1);
					}
				}
			}
			if unsafe { self.eval_unchecked(*clause.1) } == Some(false) {
				// CONFLICT
				return PropagateResult::Conflict(clause);
			} else {
				// UNIT PROPAGATION
				debug_assert!(unsafe { self.eval_unchecked(*clause.1) } == None);
				later_assigns.push((unsafe { *clause.1 }, Some(clause)));
			}
			i += 1;
		}
		PropagateResult::Ok(later_assigns)
	}
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
