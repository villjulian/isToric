def lie_derivative_mono(monomial, g, n=0):
    # This function takes a monomial and a matrix `g` as input and returns Lie derivative of the monomial with respect to `g`.
    # monomial = a monomial
    # g = a matrix, with respect to which the Lie derivative is calculated
    # n = number of variables in the ambient ring, optional argument

    if n == 0:
        n_vars = len(monomial.parent().gens())
    else:
        n_vars = n
    R = monomial.parent()
    X = matrix(R, n_vars, 1, R.gens()[:n_vars])
    gen_index = {}
    for l in range(len(R.gens())):
        gen_index[R.gens()[l]] = l
    der = 0
    for x in monomial.factor():
        l = (g[gen_index[x[0]], :] * X)[0, 0]
        der += -l * R(monomial / x[0]) * x[1]
    return der


def lie_derivative_poly(poly, g, n=0):
    # This function takes a polynomial and a matrix `g` as input, and returns Lie derivative of the polynomial with respect to `g`.
    # polynomial = a polynomial
    # g = a matrix, with respect to which the Lie derivative is calculated
    # n = number of variables in the ambient ring, optional argument

    if n == 0:
        n_vars = len(poly.parent().gens())
    else:
        n_vars = n
    der = 0
    for mon, coef in list(zip(poly.monomials(), poly.coefficients())):
        der += lie_derivative_mono(mon, g, n_vars) * coef
    return der


def get_indices(v):
    # Given a variable g_ij. As a string, they have the form gi_j. This function return i and j as integers.
    # v = a variable of shape gi_j

    s = str(v)
    l = list(s)
    mid = l.index('_')

    n1 = ''.join(l[1:mid])
    n2 = ''.join(l[mid + 1:])
    return [Integer(n1), Integer(n2)]


def eqn_to_lie_algebra(eqn, n_vars):
    # Given linear equations eqn in the g_ij, this function computes a basis of the Lie algebra.
    # eqn = list of linear equations in the g_ij
    # n_vars = number of variables in the base ring, equivalently the range of i or j.

    if (len(eqn) == 0 or eqn == [0]):
        lie = []
        for i in [0..n_vars - 1]:
            for j in [0..n_vars - 1]:
                A = zero_matrix(QQ, n_vars, n_vars)
                A[i, j] = 1
                lie.append(A)
        return lie

    Sg = eqn[0].parent()
    free_vars = list(Sg.gens())
    [free_vars.remove(s) for s in list(set([l.lm() for l in eqn]))]
    eqn1 = [l for l in eqn if l != l.lt()]
    base = []
    lie = []
    for v in free_vars:
        base = [l.lt() + l.coefficient(v) * v for l in eqn if l.coefficient(v) != 0]
        A = zero_matrix(QQ, n_vars, n_vars)
        [i, j] = get_indices(v)
        A[i - 1, j - 1] = 1
        for l in eqn:
            if (l.coefficient(v) != 0):
                [i, j] = get_indices(l.lm())
                A[i - 1, j - 1] = -l.coefficient(v) / l.lc()
        lie.append(A)
    return lie


def lie_algebra_degree(generators, n_vars, d, R, g, prog_bar):
    # The polynomials in generators are of degree <=d and there are some of degree equal to d. Computes the matrices such that (only) the degree d
    # polynomials are fixed.
    # generators = a list of polynomials of degree at most d
    # n_vars = number of variables appearing in the polynomials
    # R = polynomial ring in which the polynomials are defined and adjoint the g_ij
    # g = matrix with variables g_ij as entries
    # prog_bar = an instance of the progress_bar class used to show the progress of computations

    # S2 is a polynomial ring in the same variables as R but the entries of g are variables in the base ring. This allows us to use the command
    # coefficients later which speeds up the computations massively.

    S1 = PolynomialRing(QQ, R.gens()[n_vars:R.ngens()])
    S2 = PolynomialRing(S1, R.gens()[0:n_vars])
    phi = R.hom(S2.gens() + S1.gens(), S2)

    gens = [R(g) for g in generators]
    der_gens = []
    for gen in [gen for gen in gens if gen.degree() == d]:
        der_gens.append(lie_derivative_poly(gen, g, n_vars))
        prog_bar.update()
        prog_bar.show_progress()
    gb = R.ideal(gens).groebner_basis(deg_bound=d)
    eqn_poly = [gen.reduce(gb) for gen in der_gens]
    eqns = []
    for poly in eqn_poly:
        eqns.extend(phi(poly).coefficients())
        prog_bar.update()
        prog_bar.show_progress()
    return eqns


def commutator(a, b):
    # Computes the commutator of a and b.
    # a,b = matrices

    return a * b - b * a


def write_to_matrix(L):
    # Reshape matrices in L to vectors and write them into the rows of a matrix.
    # L = list of matrices

    m = (L[0].ncols()) ^ 2
    Z = zero_matrix(R, len(L), m)
    for i in [0..len(L) - 1]:
        Z[i, [0..m - 1]] = matrix(L[i].list())
    return Z


def gen_null_space(A, L, s=1):
    # Computes brackets [A,.] for all elements in L s times, i.e. ([A,.]^s)(L).
    # L = list of matrices
    # A = matrix

    if (s == 0):
        return L
    if (unique_ev(A) == True):
        s = 1
    Z = []
    for B in L:
        Z.append(commutator(A, B))
    return gen_null_space(A, Z, s - 1)


def basis(L):
    # Return a basis of the vector space spanned by L.
    # L = list of matrices

    if (len(L) == 0):
        return []
    n = L[0].ncols()
    Z = write_to_matrix(L)
    Z.echelonize()
    H = Z[Z.pivot_rows(), [0..Z.ncols() - 1]]
    B = []
    for i in [0..H.nrows() - 1]:
        B.append(matrix(QQ, n, n, H[i, [0..n ^ 2 - 1]].list()))
    return B


def coords(t, sub):
    # Computes the coordinates of the element t in a basis of the vector space sub.

    return matrix(sub.coordinate_vector(vector(t.list())))


def lattice_is_saturated(S):
    # Computes the lattice L defined by the binomials in S and checks if it is saturated (L\otimes_\Z \Q)\cap\Z^n = L.
    # For every binomial ax^u+bx^v the lattice generator is u-v.
    # S = set of binomials

    n = S[0].parent().ngens()
    A = matrix(ZZ, n, len(S))
    for i in [0..len(S) - 1]:
        mon = S[i].monomials()
        A[[0..n - 1], i] = matrix(ZZ, n, 1, mon[0].degrees()) - matrix(ZZ, n, 1, mon[1].degrees())
    Sm = A.smith_form()[0].diagonal()
    return Set(Sm).issubset(Set([0, 1]))


def binomial_ideal_is_prime(gb):
    # Checks if the binomial ideal generated by the Gröbner basis given in gb is prime over C.
    # gb = a reduced GB consisting of binomials

    if len(gb) == 0:
        raise RuntimeError('No elements given.')
    for poly in gb:
        if (len(poly.monomials()) > 2):
            raise RuntimeError('Input does not consist of binomials.')
    if gb.is_groebner == False:
        raise RuntimeError('Input is not a Groebner basis.')
    R = gb[0].parent()
    J = ideal(gb)
    var_in_ideal = []
    for g in R.gens():
        if (g.reduce(gb) == R(0)):
            var_in_ideal.append(g)
    if (len(var_in_ideal) > 0):
        J = J.subs({var_in_ideal[i]: 0 for i in [0..len(var_in_ideal) - 1]})
        if (J == R.ideal(0)):
            return True
        gb = J.groebner_basis()

    f = R.gens()[0]
    for i in [1..R.ngens() - 1]:
        f = f * R.gens()[i]
    if (J != J.quotient(ideal(f))):
        return False

    return lattice_is_saturated(gb)


def unique_ev(A):
    # Tests if all eigenvalues of the matrix A are distinct.
    # A = a square matrix

    ev = A.eigenvalues()
    if (len(ev) != len(set(ev))):
        return False
    else:
        return True


def is_binomial(I):
    # Tests if the ideal I can be generated by binomials (polynomials with at most two terms) and returns True or False.
    # Also returns a reduced GB of I.
    # I = an ideal

    gb = I.groebner_basis()
    for poly in gb:
        if (len(poly.monomials()) > 2):
            return [False, gb]
    return [True, gb]


def prime_rank(Z, bound, tries=10):
    # Computes the rank of Z over a small random prime field. If Z has rational entries and
    # the prime number is bad this might not work. Over a specific prime field the rank might be lower than over Q.
    # We try "tries" times to achieve the desired bound.
    # Z = matrix
    # bound = rank we try to achieve
    # tries = max depth of the recursion.

    if (tries == 0):
        return -1
    m = Z.nrows()
    n = Z.ncols()
    p = random_prime(5000, lbound=1000)
    T = MatrixSpace(GF(p), m, n)
    try:
        r = T(Z).rank()
    except Exception as ee:
        return prime_rank(Z, bound, tries=tries - 1)
    if (r == bound):
        return r
    else:
        return prime_rank(Z, bound, tries=tries - 1)


def lie_algebra_inhom(generators, prog_bar):
    # Let I be the ideal in a polynomial ring with n generators generated by the polynomials in generators and
    # let G be the subgroup of GL_{n+1} that maps I to itself. The action of GL_{n+1} on the polynomial ring
    # is given as the dual action to left multiplication on the dual space. Moreover, the first row/column is considered
    # as the "affine part".
    # This function computes the Lie algebra of the Lie group G.
    # generators = list of not necessarily homogeneous polynomials
    # prog_bar = an instance of the progress_bar class used to show the progress of computations

    if len(generators) == 0:
        raise RuntimeError('No generators given.')
    if ideal(generators).is_homogeneous():
        return lie_algebra(generators)
    S = generators[0].parent()
    gb = (S.ideal(generators)).groebner_basis()
    var = list(S.gens())
    var.insert(0, 't_hom')
    R = PolynomialRing(QQ, var, order='degrevlex')
    I = (R.ideal(gb)).homogenize(R('t_hom'))

    [gb, n_vars] = lie_algebra_eqns(I.gens(), prog_bar, inhom=True)
    return eqn_to_lie_algebra(gb, n_vars)


def lie_algebra_eqns(generators, prog_bar, inhom=False):
    # Computes the linear conditions on the elements of the Lie algebra of the group that fixes the ideal generated
    # by the elements in generators.
    # generators = list of not necessarily homogeneous polynomials
    # prog_bar = an instance of the progress_bar class used to show the progress of computations
    # inhom = False if the elements in generators are homogeneous, True if at least one is not.

    if len(generators) == 0:
        raise RuntimeError('No generators given.')
    S = generators[0].parent()
    generators_nz = [g for g in generators if g != 0]
    prog_bar.set_steps(2 * len(generators_nz))
    prog_bar.show_progress()
    n_vars = S.ngens()
    eqn = []
    var = [str(t) for t in S.gens()[:n_vars]]
    var_matrix = ['g%i_%i' % (i, j) for i in [1..n_vars] for j in [1..n_vars]]
    var += var_matrix
    R = PolynomialRing(QQ, var);
    g = matrix(R, n_vars, n_vars, R.gens()[n_vars:])
    '''
    For every degree d of some generator, we only take generators of degree at most d and compute something.
    '''
    for d in list(set([g.degree() for g in generators_nz])):
        eqn.extend(lie_algebra_degree([g for g in generators_nz if g.degree() <= d], n_vars, d, R, g, prog_bar))
    '''
    All polynomials in eqn are polynomials in the g_ij and are linear and homogeneous. The Groebner basis calculation thus terminates quickly.
    '''
    if (inhom == False):
        if (len(eqn) == 0):
            return eqn_to_lie_algebra([], n_vars)
        else:
            return [ideal(eqn).groebner_basis(), n_vars]
    else:
        if (len(eqn) == 0):
            return eqn_to_lie_algebra([], n_vars)
        Sg = eqn[0].parent()
        [eqn.append(Sg('g1_%i' % i)) for i in [2..n_vars]]
        return [ideal(eqn).groebner_basis(), n_vars]


def lie_algebra(generators):
    # Let I be the ideal in a polynomial ring with n generators generated by the polynomials in generators and
    # let G be the subgroup of GL_{n+1} that maps I to itself (or of GL_n if I is homogeneous).
    # The action of GL_{n+1} (GL_n) on the polynomial ring is given as the dual action to left multiplication
    # on the dual space. Moreover, the first row/column is considered as the "affine part" in the non-homogeneous case.
    # This function computes the Lie algebra of the Lie group G.
    # generators = list of not necessarily homogeneous polynomials

    if len(generators) == 0:
        raise RuntimeError('No generators given.')
    if generators == [0]:
        return eqn_to_lie_algebra([], generators[0].parent().ngens())
    prog_bar = progress_bar()
    if ideal(generators).is_homogeneous():
        [gb, n_vars] = lie_algebra_eqns(generators, prog_bar)
        if len(gb) == 0:
            return eqn_to_lie_algebra([], n_vars)
        return eqn_to_lie_algebra(gb, n_vars)
    else:
        return lie_algebra_inhom(generators, prog_bar)


def matrix_diagonalize(A):
    # Returns an invertible matrix S over the field of algebraic numbers diagonalizing A,
    # i.e. such that S^(-1)AS is diagonal. If the first row of S only contains one non-zero element
    # columns are swapped such that this appears in the first column.
    # A = a matrix with rational entries that is diagonalizable over the complex numbers

    B = MatrixSpace(QQbar, A.nrows(), A.ncols())(A)
    S = copy(B.eigenmatrix_right()[1])

    if A[0, :].list().count(0) == A.ncols() - 1:
        for i in [0..A.ncols() - 1]:
            if S[0, i] > 1 / 2:
                S.swap_columns(0, i)
                break
        if S[0, 0] == 1:
            return S
        else:
            for i in [0..A.ncols() - 1]:
                if S[0, i] != 0:
                    S.swap_columns(0, i)
                    break
            S[:, 0] = S[:, 0] / S[0, 0]
    return S


def ideal_diagonalize(ideal_I, S):
    # Apply the linear coordinate change given by the rows of S to the ideal ideal_I.
    # Outputs the resulting ideal in the polynomial ring over the field of algebraic numbers.
    # ideal_I = an ideal
    # S = a square matrix with the number of rows/columns agreeing with the number of variables of the ring where
    # ideal_I is defined if ideal_I is homogeneous. In the non-homogeneous case, the number of rows/columns has to be
    # larger by one.

    generators = ideal_I.gens()
    R = generators[0].parent()
    R = PolynomialRing(QQbar, R.gens())
    lifted_gens = [R(gen) for gen in generators]
    I = R.ideal(lifted_gens)
    gens = R.gens()
    if I.is_homogeneous():
        base = matrix(R, len(gens), 1, gens)
    else:
        gens = list(gens)
        gens.insert(0, R(1))
        base = matrix(R, len(gens), 1, gens)
    sub = MatrixSpace(R, S.nrows(), S.ncols())(S) * base
    J = I.subs({gens[i]: sub[i, 0] for i in [0..len(gens) - 1]})
    return J



class progress_bar:
    # This class shows a progress bar we use in the computation of the Lie algebra.

    def __init__(self):
        self.steps = 0
        self.position = 0
        self.left = 0
        self.percent = 0
        self.right = 30

    def set_steps(self, steps):
        self.steps = steps

    def show_progress(self):
        if self.percent < 100:
            print('\r[', '#' * self.left, ' ' * self.right, ']', f' {self.percent:.0f}%', sep='', end='', flush=True)
        if self.percent == 100:
            print('\r[', '#' * self.left, ' ' * self.right, ']', f' {self.percent:.0f}%\n', sep='', end='', flush=True)

    def update(self):
        self.position = self.position + 1
        self.percent = self.position * 100 // self.steps
        self.left = 30 * self.percent // 100
        self.right = 30 - self.left


def ideal_is_toric(ideal_id):
    # Decides if the ideal ideal_id is toric after some linear change of coordinates (affine linear if the ideal is
    # non-homogeneous). If this is not possible returns False.
    # If this is possible returns True and a matrix S defining a coordinate change that makes the ideal binomial.
    # ideal_id = an ideal

    lie = LieAlgebra(ideal_id)
    print('searching torus')
    t = lie.random_torus()
    print('diagonalizing torus')
    S = t.sim_diagonalize()
    print('diagonalizing ideal')
    J = ideal_diagonalize(ideal_id, S)
    print('checking if ideal is binomial and prime after the coordinate change')
    [is_bin, gb] = is_binomial(J)
    if is_bin == False:
        print('Ideal not binomial after coordinate change')
        return False
    elif binomial_ideal_is_prime(gb) == False:
        print('Ideal not prime but binomial after coordinate change.')
        return False
    else:
        return [True, S]


class LieAlgebra:

    def __init__(self, ideal_gens, gens=None):
        # initialize either with an ideal or with ideal_gens = None and a list gens consisting of matrices generating
        # a Lie algebra as a vector space.
        if (ideal_gens == None and gens == None):
            raise RuntimeError('No generators given.')
        if (ideal_gens != None and gens != None):
            raise RuntimeError('Too many generators given.')

        if (ideal_gens != None):
            self._ideal = ideal_gens
            self._basis = lie_algebra(self._ideal.gens())
        elif (gens != None):
            self._basis = basis(gens)
            # if the Lie algebra is generated in this way we do no check if this is indeed a Lie algebra,
            # ie closed under taking brackets

        self._dim = len(self._basis)

    def __repr__(self):
        return f'Lie Algebra of dimension {self._dim}.'

    def is_cartan(self, H):
        # Tests if the subalgebra H is a Cartan subalgebra.
        # H = a Lie subalgebra of self.

        if (H.nilpotent(H.basis()) == True and self.self_normalizing(H.basis()) == True):
            return True
        else:
            return False

    def nilpotent(self, H):
        # If run on input H = self.basis() tests if the Lie algebra self is nilpotent,
        # i.e. iterated brackets are zero eventually.
        # H = list of matrices

        if (len(H) == 0):
            return True
        Hp = []
        for A in self._basis:
            for B in H:
                Hp.append(commutator(A, B))
        base = basis(Hp)
        if (len(base) >= len(H)):
            return False
        return self.nilpotent(base)

    def self_normalizing(self, H):
        # Tests if the Lie algebra generated by H as a vector space is self-normalizing inside the Lie algebra self.
        # H = list of matrices

        if (len(H) == 0):
            return False
        n = len(self._basis)
        m = len(H)

        # Construct the (n+m^2) x nm-matrix Z as follows (n=len(L) and m=len(H)):
        # The first n rows contain the commutators of L[i] for i=1,...,n. More precisely, in row i we write the commutators [L[i],H[j]] one behind another.
        # This are m elements and we write their coordinates wrt to L into the matrix. This gives mn entries.
        # Denote by B the m x n matrix where in row i are the coordinates of H[i] wrt L. The lower m^2 x mn block of Z is block diagonal with m copies of B on the diagonal.

        Z = zero_matrix(QQ, n + m ^ 2, n * m, sparse=True)
        V = VectorSpace(QQ, self._basis[0].ncols() ^ 2)
        sub = V.subspace([vector(a.list()) for a in self._basis])
        for i in [0..n - 1]:
            for j in [0..m - 1]:
                Z[i, [j * n..(j + 1) * n - 1]] = coords(commutator(self._basis[i], H[j]), sub)
        coords_H = []
        for i in [0..m - 1]:
            coords_H.append(coords(H[i], sub))
        counter = n
        for i in [0..m - 1]:
            for j in [0..m - 1]:
                Z[counter, [i * n..(i + 1) * n - 1]] = coords_H[j]
                counter = counter + 1

        # The corank of Z is equal to dim{x in span(L): [x,H] subset span(H)}, i.e. the dimension of the normalizer of span(H). Since span(H) is contained in this normalizer the corank is at least dim(H).
        # If H is self-normalizing, this is exactly the corank.
        # If we find a random prime number p such that Z (which has rational entries) is defined over F_p and such that the corank over F_p is exactly dim(H) then the same holds over Q.
        # If we dont find such a prime, we compute the rank over Q. This can take a very long time since the entries of Z can be large rationals.

        if (m ^ 2 + n - prime_rank(Z, m ^ 2 + n - m) == m):
            return True
        else:
            if (m ^ 2 + n - Z.rank() == m):
                return True
            else:
                return False

    def random_cartan_algebra(self, tries=50):
        # Computes a random Cartan algebra of self.
        # This function picks a random element x in self and computes c := ker ad(x)^dim(self).
        # If x is generic c is a Cartan algebra of self.
        # This function either outputs a Cartan algebra of self or terminates with an error if the random element
        # did not give rise to a Cartan algebra 'tries' many times.
        # tries = maximum number of times a random element is picked to try and compute a Cartan algebra

        if (tries == 0):
            raise RuntimeError(
                'Recursion depth exceeded. Not able to find a Cartan algebra. Please pick a more generic element A and use cartan_algebra(A,L) instead.')

        cart = self.cartan_algebra(self.part_random_element())
        if (cart == False):
            return self.random_cartan_algebra(tries=tries - 1)
        elif cart.dimension() == self._dim:
            return self
        else:
            return cart

    def random_element(self, randomness=10):
        # Constructs a random linear combination of the basis elements of self.
        # randomness = restriction on the numerator and denominator of random rational numbers

        A = 0 * self._basis[0]
        for B in self._basis:
            A = A + B * (QQ.random_element(randomness) + QQ.random_element(randomness))
        return A

    def part_random_element(self, tries=500):
        # Constructs a random linear combination of the basis elements of self.
        # If we can find such an element with 'small' entries and simple eigenvalues such element is returned.
        # Otherwise a random element with larger entries is returned.
        # Note that a generic element does not have to have simple eigenvalues.
        # tries = number of times a linear combination with 'small' rational coefficients is checked for simple
        # eigenvalues.

        if (tries == 0):
            return self.random_element()
        A = self._basis[0]
        for B in self._basis:
            A = A + B * QQ.random_element(2)
        if (unique_ev(A) == True):
            return A
        return self.part_random_element(tries=tries - 1)

    def cartan_algebra(self, A):
        # Computes the kernel of the linear map ([A,.])^dim(self).
        # If the computed kernel is a Cartan algebra of self it is returned. Otherwise the output is False.
        # A = a matrix contained in self

        Z = write_to_matrix(gen_null_space(A, self._basis, self._dim))
        T = MatrixSpace(QQ, self._dim, (self._basis[0].ncols()) ^ 2)
        K = (T(Z).transpose()).right_kernel_matrix()
        a = []
        for i in [0..K.nrows() - 1]:
            B = 0 * self._basis[0]
            for j in [0..self._dim - 1]:
                B = B + K[i, j] * self._basis[j]
            a.append(B)
        cart = LieAlgebra(ideal_gens=None, gens=a)
        if self.is_cartan(cart):
            return cart
        else:
            return False

    def random_torus(self, cartan=False):
        # Computes a random maximal torus inside self.
        # cartan = False if self has multiple maximal tori or we do not know if this is the case. And True if
        # there is a unique maximal torus.

        if cartan == False:
            cart = self.random_cartan_algebra()
        elif cartan == True:
            cart = self
        return cart.find_torus()

    def torus_quick_test(self):
        # If there exists an element in self with simple eigenvalues and self is abelian, then self
        # is the Lie algebra of a torus.
        # If the output is True this is the case, else this criterion does not work.
        # The output False does not imply that self is not a torus.

        A = self.part_random_element()
        if unique_ev(A) == False:
            return False
        L = copy(self._basis)
        for A in L:
            for B in L:
                if commutator(A, B) != 0:
                    return False
            L.remove(A)
        return True

    def find_torus(self):
        # self has to be a Cartan algebra, in particular contain a unique maximal torus.
        # There exists a decomposition of self into t+n where t is the Lie algebra of a torus and n is a Lie algebra
        # consisting only of nilpotent elements.
        # This functions returns a basis for t.

        # Instead of checking if every element is diagonalizable we perform a quick test that often works and
        # relies on finding an element with simple eigenvalues.

        if self.torus_quick_test() == True:
            return self

        n = self._basis[0].ncols()
        L = []
        MM = MatrixSpace(QQbar, n, n)
        counter = 0
        for A in self._basis:
            if (MM(A).is_diagonalizable() == False):
                jd = MM(A).jordan_form(transformation=True)
                D = copy(jd[0])
                B = copy(jd[1])
                for j1 in [0..n - 1]:
                    for j2 in [j1 + 1..n - 1]:
                        D[j1, j2] = QQbar(0)
                L.append((B * D * B.inverse()))
            else:
                L.append(A)
        base = basis(L)
        if (len(base) == self._dim):
            return self
        return LieAlgebra(ideal_gens=None, gens=basis(L))

    def sim_diagonalize(self):
        # This function should only be used if self is a toral Lie algebra. In this case a matrix S is returned
        # that simultaneously diagonalizes the basis of self. This is done by picking a random element and checking
        # afterward if had the correct properties. If the element was not generic enough, this function terminates
        # with an error.

        A = self.part_random_element()
        if unique_ev(A):
            return matrix_diagonalize(A)
        else:
            S = matrix_diagonalize(A)
            if self.diagonalizes_torus(S):
                return S
            else:
                raise RuntimeError('The random element was not generic enough. Run the function again.')

    def diagonalizes_torus(self, S):
        # Tests if the matrix S diagonalizes every basis element of self.
        # S = invertible matrix
        
        for A in self._basis:
            if ((S.adjugate() * A * S).is_diagonal() == False):
                return False
        return True

    def dimension(self):
        return self._dim

    def basis(self):
        return self._basis

    def intersection(self, L):
    	# Computes the intersection of self with the Lie algebra L.
    	# L = a Lie algebra
    	
        join = []
        for A in self._basis:
            join.append(A)
        for A in L.basis():
            join.append(A)

        Z = write_to_matrix(join)
        K = Z.left_kernel_matrix()

        intersection_matrix = copy(K)
        K[:,[self._dim..len(join)-1]] = zero_matrix(QQ,K.nrows(),L.dimension())
        
        intersection = K*Z

        H = []
        for i in [0..intersection.nrows()-1]:
            H.append(matrix(QQ,self._basis[0].nrows(), self._basis[0].nrows(), intersection[i,:].list()))

        return LieAlgebra(ideal_gens=None, gens=H)

