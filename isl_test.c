/*
 * Copyright 2008-2009 Katholieke Universiteit Leuven
 * Copyright 2010      INRIA Saclay
 * Copyright 2012-2013 Ecole Normale Superieure
 * Copyright 2014      INRIA Rocquencourt
 *
 * Use of this software is governed by the MIT license
 *
 * Written by Sven Verdoolaege, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 * and INRIA Saclay - Ile-de-France, Parc Club Orsay Universite,
 * ZAC des vignes, 4 rue Jacques Monod, 91893 Orsay, France
 * and Ecole Normale Superieure, 45 rue d’Ulm, 75230 Paris, France
 * and Inria Paris - Rocquencourt, Domaine de Voluceau - Rocquencourt,
 * B.P. 105 - 78153 Le Chesnay, France
 */

#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <isl_ctx_private.h>
#include <isl_map_private.h>
#include <isl_aff_private.h>
#include <isl_space_private.h>
#include <isl/id.h>
#include <isl/set.h>
#include <isl/flow.h>
#include <isl_constraint_private.h>
#include <isl/polynomial.h>
#include <isl/union_set.h>
#include <isl/union_map.h>
#include <isl_factorization.h>
#include <isl/schedule.h>
#include <isl/schedule_node.h>
#include <isl_options_private.h>
#include <isl_vertices_private.h>
#include <isl/ast_build.h>
#include <isl/val.h>
#include <isl/ilp.h>
#include <isl_ast_build_expr.h>
#include <isl/options.h>

#include "isl_srcdir.c"

#define ARRAY_SIZE(array) (sizeof(array)/sizeof(*array))

static isl_stat check_injective(__isl_take isl_map *map, void *user)
{
	int *injective = user;

	*injective = isl_map_is_injective(map);
	isl_map_free(map);

	if (*injective < 0 || !*injective)
		return isl_stat_error;

	return isl_stat_ok;
}

int test_one_schedule(isl_ctx *ctx, const char *d, const char *w,
	const char *r, const char *s, int tilable, int parallel)
{
	int i;
	isl_union_set *D;
	isl_union_map *W, *R, *S;
	isl_union_map *empty;
	isl_union_map *dep_raw, *dep_war, *dep_waw, *dep;
	isl_union_map *validity, *proximity, *coincidence;
	isl_union_map *schedule;
	isl_union_map *test;
	isl_union_set *delta;
	isl_union_set *domain;
	isl_set *delta_set;
	isl_set *slice;
	isl_set *origin;
	isl_schedule_constraints *sc;
	isl_schedule *sched;
	int is_nonneg, is_parallel, is_tilable, is_injection, is_complete;
	isl_size n;

	D = isl_union_set_read_from_str(ctx, d);
	W = isl_union_map_read_from_str(ctx, w);
	R = isl_union_map_read_from_str(ctx, r);
	S = isl_union_map_read_from_str(ctx, s);

	W = isl_union_map_intersect_domain(W, isl_union_set_copy(D));
	R = isl_union_map_intersect_domain(R, isl_union_set_copy(D));

	empty = isl_union_map_empty(isl_union_map_get_space(S));
        isl_union_map_compute_flow(isl_union_map_copy(R),
				   isl_union_map_copy(W), empty,
				   isl_union_map_copy(S),
				   &dep_raw, NULL, NULL, NULL);
        isl_union_map_compute_flow(isl_union_map_copy(W),
				   isl_union_map_copy(W),
				   isl_union_map_copy(R),
				   isl_union_map_copy(S),
				   &dep_waw, &dep_war, NULL, NULL);

	dep = isl_union_map_union(dep_waw, dep_war);
	dep = isl_union_map_union(dep, dep_raw);
	validity = isl_union_map_copy(dep);
	coincidence = isl_union_map_copy(dep);
	proximity = isl_union_map_copy(dep);

	sc = isl_schedule_constraints_on_domain(isl_union_set_copy(D));
	sc = isl_schedule_constraints_set_validity(sc, validity);
	sc = isl_schedule_constraints_set_coincidence(sc, coincidence);
	sc = isl_schedule_constraints_set_proximity(sc, proximity);
	sched = isl_schedule_constraints_compute_schedule(sc);
	schedule = isl_schedule_get_map(sched);
	isl_schedule_free(sched);
	isl_union_map_free(W);
	isl_union_map_free(R);
	isl_union_map_free(S);

	is_injection = 1;
	isl_union_map_foreach_map(schedule, &check_injective, &is_injection);

	domain = isl_union_map_domain(isl_union_map_copy(schedule));
	is_complete = isl_union_set_is_subset(D, domain);
	isl_union_set_free(D);
	isl_union_set_free(domain);

	test = isl_union_map_reverse(isl_union_map_copy(schedule));
	test = isl_union_map_apply_range(test, dep);
	test = isl_union_map_apply_range(test, schedule);

	delta = isl_union_map_deltas(test);
	n = isl_union_set_n_set(delta);
	if (n < 0) {
		isl_union_set_free(delta);
		return -1;
	}
	if (n == 0) {
		is_tilable = 1;
		is_parallel = 1;
		is_nonneg = 1;
		isl_union_set_free(delta);
	} else {
		isl_size dim;

		delta_set = isl_set_from_union_set(delta);

		slice = isl_set_universe(isl_set_get_space(delta_set));
		for (i = 0; i < tilable; ++i)
			slice = isl_set_lower_bound_si(slice, isl_dim_set, i, 0);
		is_tilable = isl_set_is_subset(delta_set, slice);
		isl_set_free(slice);

		slice = isl_set_universe(isl_set_get_space(delta_set));
		for (i = 0; i < parallel; ++i)
			slice = isl_set_fix_si(slice, isl_dim_set, i, 0);
		is_parallel = isl_set_is_subset(delta_set, slice);
		isl_set_free(slice);

		origin = isl_set_universe(isl_set_get_space(delta_set));
		dim = isl_set_dim(origin, isl_dim_set);
		if (dim < 0)
			origin = isl_set_free(origin);
		for (i = 0; i < dim; ++i)
			origin = isl_set_fix_si(origin, isl_dim_set, i, 0);

		delta_set = isl_set_union(delta_set, isl_set_copy(origin));
		delta_set = isl_set_lexmin(delta_set);

		is_nonneg = isl_set_is_equal(delta_set, origin);

		isl_set_free(origin);
		isl_set_free(delta_set);
	}

	if (is_nonneg < 0 || is_parallel < 0 || is_tilable < 0 ||
	    is_injection < 0 || is_complete < 0)
		return -1;
	if (!is_complete)
		isl_die(ctx, isl_error_unknown,
			"generated schedule incomplete", return -1);
	if (!is_injection)
		isl_die(ctx, isl_error_unknown,
			"generated schedule not injective on each statement",
			return -1);
	if (!is_nonneg)
		isl_die(ctx, isl_error_unknown,
			"negative dependences in generated schedule",
			return -1);
	if (!is_tilable)
		isl_die(ctx, isl_error_unknown,
			"generated schedule not as tilable as expected",
			return -1);
	if (!is_parallel)
		isl_die(ctx, isl_error_unknown,
			"generated schedule not as parallel as expected",
			return -1);

	return 0;
}

/* Compute a schedule for the given instance set, validity constraints,
 * proximity constraints and context and return a corresponding union map
 * representation.
 */
static __isl_give isl_union_map *compute_schedule_with_context(isl_ctx *ctx,
	const char *domain, const char *validity, const char *proximity,
	const char *context)
{
	isl_set *con;
	isl_union_set *dom;
	isl_union_map *dep;
	isl_union_map *prox;
	isl_schedule_constraints *sc;
	isl_schedule *schedule;
	isl_union_map *sched;

	con = isl_set_read_from_str(ctx, context);
	dom = isl_union_set_read_from_str(ctx, domain);
	dep = isl_union_map_read_from_str(ctx, validity);
	prox = isl_union_map_read_from_str(ctx, proximity);
	sc = isl_schedule_constraints_on_domain(dom);
	sc = isl_schedule_constraints_set_context(sc, con);
	sc = isl_schedule_constraints_set_validity(sc, dep);
	sc = isl_schedule_constraints_set_proximity(sc, prox);
	schedule = isl_schedule_constraints_compute_schedule(sc);
	sched = isl_schedule_get_map(schedule);
	isl_schedule_free(schedule);

	return sched;
}

/* Compute a schedule for the given instance set, validity constraints and
 * proximity constraints and return a corresponding union map representation.
 */
static __isl_give isl_union_map *compute_schedule(isl_ctx *ctx,
	const char *domain, const char *validity, const char *proximity)
{
	return compute_schedule_with_context(ctx, domain, validity, proximity,
						"{ : }");
}

/* Check that a schedule can be constructed on the given domain
 * with the given validity and proximity constraints.
 */
static int test_has_schedule(isl_ctx *ctx, const char *domain,
	const char *validity, const char *proximity)
{
	isl_union_map *sched;

	sched = compute_schedule(ctx, domain, validity, proximity);
	if (!sched)
		return -1;

	isl_union_map_free(sched);
	return 0;
}

int test_special_schedule(isl_ctx *ctx, const char *domain,
	const char *validity, const char *proximity, const char *expected_sched)
{
	isl_union_map *sched1, *sched2;
	int equal;

	sched1 = compute_schedule(ctx, domain, validity, proximity);
	sched2 = isl_union_map_read_from_str(ctx, expected_sched);

	equal = isl_union_map_is_equal(sched1, sched2);
	isl_union_map_free(sched1);
	isl_union_map_free(sched2);

	if (equal < 0)
		return -1;
	if (!equal)
		isl_die(ctx, isl_error_unknown, "unexpected schedule",
			return -1);

	return 0;
}

/* Check that the schedule map is properly padded, i.e., that the range
 * lives in a single space.
 */
static int test_padded_schedule(isl_ctx *ctx)
{
	const char *str;
	isl_union_set *D;
	isl_union_map *validity, *proximity;
	isl_schedule_constraints *sc;
	isl_schedule *sched;
	isl_union_map *umap;
	isl_union_set *range;
	isl_set *set;

	str = "[N] -> { S0[i] : 0 <= i <= N; S1[i, j] : 0 <= i, j <= N }";
	D = isl_union_set_read_from_str(ctx, str);
	validity = isl_union_map_empty(isl_union_set_get_space(D));
	proximity = isl_union_map_copy(validity);
	sc = isl_schedule_constraints_on_domain(D);
	sc = isl_schedule_constraints_set_validity(sc, validity);
	sc = isl_schedule_constraints_set_proximity(sc, proximity);
	sched = isl_schedule_constraints_compute_schedule(sc);
	umap = isl_schedule_get_map(sched);
	isl_schedule_free(sched);
	range = isl_union_map_range(umap);
	set = isl_set_from_union_set(range);
	isl_set_free(set);

	if (!set)
		return -1;

	return 0;
}

/* Check that conditional validity constraints are also taken into
 * account across bands.
 * In particular, try to make sure that live ranges D[1,0]->C[2,1] and
 * D[2,0]->C[3,0] are not local in the outer band of the generated schedule
 * and then check that the adjacent order constraint C[2,1]->D[2,0]
 * is enforced by the rest of the schedule.
 */
static int test_special_conditional_schedule_constraints(isl_ctx *ctx)
{
	const char *str;
	isl_union_set *domain;
	isl_union_map *validity, *proximity, *condition;
	isl_union_map *sink, *source, *dep;
	isl_schedule_constraints *sc;
	isl_schedule *schedule;
	isl_union_access_info *access;
	isl_union_flow *flow;
	int empty;

	str = "[n] -> { C[k, i] : k <= -1 + n and i >= 0 and i <= -1 + k; "
	    "A[k] : k >= 1 and k <= -1 + n; "
	    "B[k, i] : k <= -1 + n and i >= 0 and i <= -1 + k; "
	    "D[k, i] : k <= -1 + n and i >= 0 and i <= -1 + k }";
	domain = isl_union_set_read_from_str(ctx, str);
	sc = isl_schedule_constraints_on_domain(domain);
	str = "[n] -> { D[k, i] -> C[1 + k, k - i] : "
		"k <= -2 + n and i >= 1 and i <= -1 + k; "
		"D[k, i] -> C[1 + k, i] : "
		"k <= -2 + n and i >= 1 and i <= -1 + k; "
		"D[k, 0] -> C[1 + k, k] : k >= 1 and k <= -2 + n; "
		"D[k, 0] -> C[1 + k, 0] : k >= 1 and k <= -2 + n }";
	validity = isl_union_map_read_from_str(ctx, str);
	sc = isl_schedule_constraints_set_validity(sc, validity);
	str = "[n] -> { C[k, i] -> D[k, i] : "
		"0 <= i <= -1 + k and k <= -1 + n }";
	proximity = isl_union_map_read_from_str(ctx, str);
	sc = isl_schedule_constraints_set_proximity(sc, proximity);
	str = "[n] -> { [D[k, i] -> a[]] -> [C[1 + k, k - i] -> b[]] : "
		"i <= -1 + k and i >= 1 and k <= -2 + n; "
		"[B[k, i] -> c[]] -> [B[k, 1 + i] -> c[]] : "
		"k <= -1 + n and i >= 0 and i <= -2 + k }";
	condition = isl_union_map_read_from_str(ctx, str);
	str = "[n] -> { [B[k, i] -> e[]] -> [D[k, i] -> a[]] : "
		"i >= 0 and i <= -1 + k and k <= -1 + n; "
		"[C[k, i] -> b[]] -> [D[k', -1 + k - i] -> a[]] : "
		"i >= 0 and i <= -1 + k and k <= -1 + n and "
		"k' <= -1 + n and k' >= k - i and k' >= 1 + k; "
		"[C[k, i] -> b[]] -> [D[k, -1 + k - i] -> a[]] : "
		"i >= 0 and i <= -1 + k and k <= -1 + n; "
		"[B[k, i] -> c[]] -> [A[k'] -> d[]] : "
		"k <= -1 + n and i >= 0 and i <= -1 + k and "
		"k' >= 1 and k' <= -1 + n and k' >= 1 + k }";
	validity = isl_union_map_read_from_str(ctx, str);
	sc = isl_schedule_constraints_set_conditional_validity(sc, condition,
								validity);
	schedule = isl_schedule_constraints_compute_schedule(sc);
	str = "{ D[2,0] -> [] }";
	sink = isl_union_map_read_from_str(ctx, str);
	access = isl_union_access_info_from_sink(sink);
	str = "{ C[2,1] -> [] }";
	source = isl_union_map_read_from_str(ctx, str);
	access = isl_union_access_info_set_must_source(access, source);
	access = isl_union_access_info_set_schedule(access, schedule);
	flow = isl_union_access_info_compute_flow(access);
	dep = isl_union_flow_get_must_dependence(flow);
	isl_union_flow_free(flow);
	empty = isl_union_map_is_empty(dep);
	isl_union_map_free(dep);

	if (empty < 0)
		return -1;
	if (empty)
		isl_die(ctx, isl_error_unknown,
			"conditional validity not respected", return -1);

	return 0;
}

/* Check that the test for violated conditional validity constraints
 * is not confused by domain compression.
 * In particular, earlier versions of isl would apply
 * a schedule on the compressed domains to the original domains,
 * resulting in a failure to detect that the default schedule
 * violates the conditional validity constraints.
 */
static int test_special_conditional_schedule_constraints_2(isl_ctx *ctx)
{
	const char *str;
	isl_bool empty;
	isl_union_set *domain;
	isl_union_map *validity, *condition;
	isl_schedule_constraints *sc;
	isl_schedule *schedule;
	isl_union_map *umap;
	isl_map *map, *ge;

	str = "{ A[0, i] : 0 <= i <= 10; B[1, i] : 0 <= i <= 10 }";
	domain = isl_union_set_read_from_str(ctx, str);
	sc = isl_schedule_constraints_on_domain(domain);
	str = "{ B[1, i] -> A[0, i + 1] }";
	condition = isl_union_map_read_from_str(ctx, str);
	str = "{ A[0, i] -> B[1, i - 1] }";
	validity = isl_union_map_read_from_str(ctx, str);
	sc = isl_schedule_constraints_set_conditional_validity(sc, condition,
						isl_union_map_copy(validity));
	schedule = isl_schedule_constraints_compute_schedule(sc);
	umap = isl_schedule_get_map(schedule);
	isl_schedule_free(schedule);
	validity = isl_union_map_apply_domain(validity,
						isl_union_map_copy(umap));
	validity = isl_union_map_apply_range(validity, umap);
	map = isl_map_from_union_map(validity);
	ge = isl_map_lex_ge(isl_space_domain(isl_map_get_space(map)));
	map = isl_map_intersect(map, ge);
	empty = isl_map_is_empty(map);
	isl_map_free(map);

	if (empty < 0)
		return -1;
	if (!empty)
		isl_die(ctx, isl_error_unknown,
			"conditional validity constraints not satisfied",
			return -1);

	return 0;
}

/* Input for testing of schedule construction based on
 * conditional constraints.
 *
 * domain is the iteration domain
 * flow are the flow dependences, which determine the validity and
 * 	proximity constraints
 * condition are the conditions on the conditional validity constraints
 * conditional_validity are the conditional validity constraints
 * outer_band_n is the expected number of members in the outer band
 */
struct {
	const char *domain;
	const char *flow;
	const char *condition;
	const char *conditional_validity;
	int outer_band_n;
} live_range_tests[] = {
	/* Contrived example that illustrates that we need to keep
	 * track of tagged condition dependences and
	 * tagged conditional validity dependences
	 * in isl_sched_edge separately.
	 * In particular, the conditional validity constraints on A
	 * cannot be satisfied,
	 * but they can be ignored because there are no corresponding
	 * condition constraints.  However, we do have an additional
	 * conditional validity constraint that maps to the same
	 * dependence relation
	 * as the condition constraint on B.  If we did not make a distinction
	 * between tagged condition and tagged conditional validity
	 * dependences, then we
	 * could end up treating this shared dependence as an condition
	 * constraint on A, forcing a localization of the conditions,
	 * which is impossible.
	 */
	{ "{ S[i] : 0 <= 1 < 100; T[i] : 0 <= 1 < 100 }",
	  "{ S[i] -> S[i+1] : 0 <= i < 99 }",
	  "{ [S[i] -> B[]] -> [S[i+1] -> B[]] : 0 <= i < 99 }",
	  "{ [S[i] -> A[]] -> [T[i'] -> A[]] : 0 <= i', i < 100 and i != i';"
	    "[T[i] -> A[]] -> [S[i'] -> A[]] : 0 <= i', i < 100 and i != i';"
	    "[S[i] -> A[]] -> [S[i+1] -> A[]] : 0 <= i < 99 }",
	  1
	},
	/* TACO 2013 Fig. 7 */
	{ "[n] -> { S1[i,j] : 0 <= i,j < n; S2[i,j] : 0 <= i,j < n }",
	  "[n] -> { S1[i,j] -> S2[i,j] : 0 <= i,j < n;"
		   "S2[i,j] -> S2[i,j+1] : 0 <= i < n and 0 <= j < n - 1 }",
	  "[n] -> { [S1[i,j] -> t[]] -> [S2[i,j] -> t[]] : 0 <= i,j < n;"
		   "[S2[i,j] -> x1[]] -> [S2[i,j+1] -> x1[]] : "
				"0 <= i < n and 0 <= j < n - 1 }",
	  "[n] -> { [S2[i,j] -> t[]] -> [S1[i,j'] -> t[]] : "
				"0 <= i < n and 0 <= j < j' < n;"
		   "[S2[i,j] -> t[]] -> [S1[i',j'] -> t[]] : "
				"0 <= i < i' < n and 0 <= j,j' < n;"
		   "[S2[i,j] -> x1[]] -> [S2[i,j'] -> x1[]] : "
				"0 <= i,j,j' < n and j < j' }",
	    2
	},
	/* TACO 2013 Fig. 7, without tags */
	{ "[n] -> { S1[i,j] : 0 <= i,j < n; S2[i,j] : 0 <= i,j < n }",
	  "[n] -> { S1[i,j] -> S2[i,j] : 0 <= i,j < n;"
		   "S2[i,j] -> S2[i,j+1] : 0 <= i < n and 0 <= j < n - 1 }",
	  "[n] -> { S1[i,j] -> S2[i,j] : 0 <= i,j < n;"
		   "S2[i,j] -> S2[i,j+1] : 0 <= i < n and 0 <= j < n - 1 }",
	  "[n] -> { S2[i,j] -> S1[i,j'] : 0 <= i < n and 0 <= j < j' < n;"
		   "S2[i,j] -> S1[i',j'] : 0 <= i < i' < n and 0 <= j,j' < n;"
		   "S2[i,j] -> S2[i,j'] : 0 <= i,j,j' < n and j < j' }",
	   1
	},
	/* TACO 2013 Fig. 12 */
	{ "{ S1[i,0] : 0 <= i <= 1; S2[i,j] : 0 <= i <= 1 and 1 <= j <= 2;"
	    "S3[i,3] : 0 <= i <= 1 }",
	  "{ S1[i,0] -> S2[i,1] : 0 <= i <= 1;"
	    "S2[i,1] -> S2[i,2] : 0 <= i <= 1;"
	    "S2[i,2] -> S3[i,3] : 0 <= i <= 1 }",
	  "{ [S1[i,0]->t[]] -> [S2[i,1]->t[]] : 0 <= i <= 1;"
	    "[S2[i,1]->t[]] -> [S2[i,2]->t[]] : 0 <= i <= 1;"
	    "[S2[i,2]->t[]] -> [S3[i,3]->t[]] : 0 <= i <= 1 }",
	  "{ [S2[i,1]->t[]] -> [S2[i,2]->t[]] : 0 <= i <= 1;"
	    "[S2[0,j]->t[]] -> [S2[1,j']->t[]] : 1 <= j,j' <= 2;"
	    "[S2[0,j]->t[]] -> [S1[1,0]->t[]] : 1 <= j <= 2;"
	    "[S3[0,3]->t[]] -> [S2[1,j]->t[]] : 1 <= j <= 2;"
	    "[S3[0,3]->t[]] -> [S1[1,0]->t[]] }",
	   1
	}
};

/* Test schedule construction based on conditional constraints.
 * In particular, check the number of members in the outer band node
 * as an indication of whether tiling is possible or not.
 */
static int test_conditional_schedule_constraints(isl_ctx *ctx)
{
	int i;
	isl_union_set *domain;
	isl_union_map *condition;
	isl_union_map *flow;
	isl_union_map *validity;
	isl_schedule_constraints *sc;
	isl_schedule *schedule;
	isl_schedule_node *node;
	isl_size n_member;

	if (test_special_conditional_schedule_constraints(ctx) < 0)
		return -1;
	if (test_special_conditional_schedule_constraints_2(ctx) < 0)
		return -1;

	for (i = 0; i < ARRAY_SIZE(live_range_tests); ++i) {
		domain = isl_union_set_read_from_str(ctx,
				live_range_tests[i].domain);
		flow = isl_union_map_read_from_str(ctx,
				live_range_tests[i].flow);
		condition = isl_union_map_read_from_str(ctx,
				live_range_tests[i].condition);
		validity = isl_union_map_read_from_str(ctx,
				live_range_tests[i].conditional_validity);
		sc = isl_schedule_constraints_on_domain(domain);
		sc = isl_schedule_constraints_set_validity(sc,
				isl_union_map_copy(flow));
		sc = isl_schedule_constraints_set_proximity(sc, flow);
		sc = isl_schedule_constraints_set_conditional_validity(sc,
				condition, validity);
		schedule = isl_schedule_constraints_compute_schedule(sc);
		node = isl_schedule_get_root(schedule);
		while (node &&
		    isl_schedule_node_get_type(node) != isl_schedule_node_band)
			node = isl_schedule_node_first_child(node);
		n_member = isl_schedule_node_band_n_member(node);
		isl_schedule_node_free(node);
		isl_schedule_free(schedule);

		if (!schedule || n_member < 0)
			return -1;
		if (n_member != live_range_tests[i].outer_band_n)
			isl_die(ctx, isl_error_unknown,
				"unexpected number of members in outer band",
				return -1);
	}
	return 0;
}

/* Check that the schedule computed for the given instance set and
 * dependence relation strongly satisfies the dependences.
 * In particular, check that no instance is scheduled before
 * or together with an instance on which it depends.
 * Earlier versions of isl would produce a schedule that
 * only weakly satisfies the dependences.
 */
static int test_strongly_satisfying_schedule(isl_ctx *ctx)
{
	const char *domain, *dep;
	isl_union_map *D, *schedule;
	isl_map *map, *ge;
	int empty;

	domain = "{ B[i0, i1] : 0 <= i0 <= 1 and 0 <= i1 <= 11; "
		    "A[i0] : 0 <= i0 <= 1 }";
	dep = "{ B[i0, i1] -> B[i0, 1 + i1] : 0 <= i0 <= 1 and 0 <= i1 <= 10; "
		"B[0, 11] -> A[1]; A[i0] -> B[i0, 0] : 0 <= i0 <= 1 }";
	schedule = compute_schedule(ctx, domain, dep, dep);
	D = isl_union_map_read_from_str(ctx, dep);
	D = isl_union_map_apply_domain(D, isl_union_map_copy(schedule));
	D = isl_union_map_apply_range(D, schedule);
	map = isl_map_from_union_map(D);
	ge = isl_map_lex_ge(isl_space_domain(isl_map_get_space(map)));
	map = isl_map_intersect(map, ge);
	empty = isl_map_is_empty(map);
	isl_map_free(map);

	if (empty < 0)
		return -1;
	if (!empty)
		isl_die(ctx, isl_error_unknown,
			"dependences not strongly satisfied", return -1);

	return 0;
}

/* Compute a schedule for input where the instance set constraints
 * conflict with the context constraints.
 * Earlier versions of isl did not properly handle this situation.
 */
static int test_conflicting_context_schedule(isl_ctx *ctx)
{
	isl_union_map *schedule;
	const char *domain, *context;

	domain = "[n] -> { A[] : n >= 0 }";
	context = "[n] -> { : n < 0 }";
	schedule = compute_schedule_with_context(ctx,
						domain, "{}", "{}", context);
	isl_union_map_free(schedule);

	if (!schedule)
		return -1;

	return 0;
}

/* Check that a set of schedule constraints that only allow for
 * a coalescing schedule still produces a schedule even if the user
 * request a non-coalescing schedule.  Earlier versions of isl
 * would not handle this case correctly.
 */
static int test_coalescing_schedule(isl_ctx *ctx)
{
	const char *domain, *dep;
	isl_union_set *I;
	isl_union_map *D;
	isl_schedule_constraints *sc;
	isl_schedule *schedule;
	int treat_coalescing;

	domain = "{ S[a, b] : 0 <= a <= 1 and 0 <= b <= 1 }";
	dep = "{ S[a, b] -> S[a + b, 1 - b] }";
	I = isl_union_set_read_from_str(ctx, domain);
	D = isl_union_map_read_from_str(ctx, dep);
	sc = isl_schedule_constraints_on_domain(I);
	sc = isl_schedule_constraints_set_validity(sc, D);
	treat_coalescing = isl_options_get_schedule_treat_coalescing(ctx);
	isl_options_set_schedule_treat_coalescing(ctx, 1);
	schedule = isl_schedule_constraints_compute_schedule(sc);
	isl_options_set_schedule_treat_coalescing(ctx, treat_coalescing);
	isl_schedule_free(schedule);
	if (!schedule)
		return -1;
	return 0;
}

/* Check that the scheduler does not perform any needless
 * compound skewing.  Earlier versions of isl would compute
 * schedules in terms of transformed schedule coefficients and
 * would not accurately keep track of the sum of the original
 * schedule coefficients.  It could then produce the schedule
 * S[t,i,j,k] -> [t, 2t + i, 2t + i + j, 2t + i + j + k]
 * for the input below instead of the schedule below.
 */
static int test_skewing_schedule(isl_ctx *ctx)
{
	const char *D, *V, *P, *S;

	D = "[n] -> { S[t,i,j,k] : 0 <= t,i,j,k < n }";
	V = "[n] -> { S[t,i,j,k] -> S[t+1,a,b,c] : 0 <= t,i,j,k,a,b,c < n and "
		"-2 <= a-i <= 2 and -1 <= a-i + b-j <= 1 and "
		"-1 <= a-i + b-j + c-k <= 1 }";
	P = "{ }";
	S = "{ S[t,i,j,k] -> [t, 2t + i, t + i + j, 2t + k] }";

	return test_special_schedule(ctx, D, V, P, S);
}

int test_schedule(isl_ctx *ctx)
{
	const char *D, *W, *R, *V, *P, *S;
	int max_coincidence;
	int treat_coalescing;

	/* Handle resulting schedule with zero bands. */
	if (test_one_schedule(ctx, "{[]}", "{}", "{}", "{[] -> []}", 0, 0) < 0)
		return -1;

	/* Jacobi */
	D = "[T,N] -> { S1[t,i] : 1 <= t <= T and 2 <= i <= N - 1 }";
	W = "{ S1[t,i] -> a[t,i] }";
	R = "{ S1[t,i] -> a[t-1,i]; S1[t,i] -> a[t-1,i-1]; "
	    	"S1[t,i] -> a[t-1,i+1] }";
	S = "{ S1[t,i] -> [t,i] }";
	if (test_one_schedule(ctx, D, W, R, S, 2, 0) < 0)
		return -1;

	/* Fig. 5 of CC2008 */
	D = "[N] -> { S_0[i, j] : i >= 0 and i <= -1 + N and j >= 2 and "
				"j <= -1 + N }";
	W = "[N] -> { S_0[i, j] -> a[i, j] : i >= 0 and i <= -1 + N and "
				"j >= 2 and j <= -1 + N }";
	R = "[N] -> { S_0[i, j] -> a[j, i] : i >= 0 and i <= -1 + N and "
				"j >= 2 and j <= -1 + N; "
		    "S_0[i, j] -> a[i, -1 + j] : i >= 0 and i <= -1 + N and "
				"j >= 2 and j <= -1 + N }";
	S = "[N] -> { S_0[i, j] -> [0, i, 0, j, 0] }";
	if (test_one_schedule(ctx, D, W, R, S, 2, 0) < 0)
		return -1;

	D = "{ S1[i] : 0 <= i <= 10; S2[i] : 0 <= i <= 9 }";
	W = "{ S1[i] -> a[i] }";
	R = "{ S2[i] -> a[i+1] }";
	S = "{ S1[i] -> [0,i]; S2[i] -> [1,i] }";
	if (test_one_schedule(ctx, D, W, R, S, 1, 1) < 0)
		return -1;

	D = "{ S1[i] : 0 <= i < 10; S2[i] : 0 <= i < 10 }";
	W = "{ S1[i] -> a[i] }";
	R = "{ S2[i] -> a[9-i] }";
	S = "{ S1[i] -> [0,i]; S2[i] -> [1,i] }";
	if (test_one_schedule(ctx, D, W, R, S, 1, 1) < 0)
		return -1;

	D = "[N] -> { S1[i] : 0 <= i < N; S2[i] : 0 <= i < N }";
	W = "{ S1[i] -> a[i] }";
	R = "[N] -> { S2[i] -> a[N-1-i] }";
	S = "{ S1[i] -> [0,i]; S2[i] -> [1,i] }";
	if (test_one_schedule(ctx, D, W, R, S, 1, 1) < 0)
		return -1;
	
	D = "{ S1[i] : 0 < i < 10; S2[i] : 0 <= i < 10 }";
	W = "{ S1[i] -> a[i]; S2[i] -> b[i] }";
	R = "{ S2[i] -> a[i]; S1[i] -> b[i-1] }";
	S = "{ S1[i] -> [i,0]; S2[i] -> [i,1] }";
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;

	D = "[N] -> { S1[i] : 1 <= i <= N; S2[i,j] : 1 <= i,j <= N }";
	W = "{ S1[i] -> a[0,i]; S2[i,j] -> a[i,j] }";
	R = "{ S2[i,j] -> a[i-1,j] }";
	S = "{ S1[i] -> [0,i,0]; S2[i,j] -> [1,i,j] }";
	if (test_one_schedule(ctx, D, W, R, S, 2, 1) < 0)
		return -1;

	D = "[N] -> { S1[i] : 1 <= i <= N; S2[i,j] : 1 <= i,j <= N }";
	W = "{ S1[i] -> a[i,0]; S2[i,j] -> a[i,j] }";
	R = "{ S2[i,j] -> a[i,j-1] }";
	S = "{ S1[i] -> [0,i,0]; S2[i,j] -> [1,i,j] }";
	if (test_one_schedule(ctx, D, W, R, S, 2, 1) < 0)
		return -1;

	D = "[N] -> { S_0[]; S_1[i] : i >= 0 and i <= -1 + N; S_2[] }";
	W = "[N] -> { S_0[] -> a[0]; S_2[] -> b[0]; "
		    "S_1[i] -> a[1 + i] : i >= 0 and i <= -1 + N }";
	R = "[N] -> { S_2[] -> a[N]; S_1[i] -> a[i] : i >= 0 and i <= -1 + N }";
	S = "[N] -> { S_1[i] -> [1, i, 0]; S_2[] -> [2, 0, 1]; "
		    "S_0[] -> [0, 0, 0] }";
	if (test_one_schedule(ctx, D, W, R, S, 1, 0) < 0)
		return -1;
	ctx->opt->schedule_parametric = 0;
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;
	ctx->opt->schedule_parametric = 1;

	D = "[N] -> { S1[i] : 1 <= i <= N; S2[i] : 1 <= i <= N; "
		    "S3[i,j] : 1 <= i,j <= N; S4[i] : 1 <= i <= N }";
	W = "{ S1[i] -> a[i,0]; S2[i] -> a[0,i]; S3[i,j] -> a[i,j] }";
	R = "[N] -> { S3[i,j] -> a[i-1,j]; S3[i,j] -> a[i,j-1]; "
		    "S4[i] -> a[i,N] }";
	S = "{ S1[i] -> [0,i,0]; S2[i] -> [1,i,0]; S3[i,j] -> [2,i,j]; "
		"S4[i] -> [4,i,0] }";
	max_coincidence = isl_options_get_schedule_maximize_coincidence(ctx);
	isl_options_set_schedule_maximize_coincidence(ctx, 0);
	if (test_one_schedule(ctx, D, W, R, S, 2, 0) < 0)
		return -1;
	isl_options_set_schedule_maximize_coincidence(ctx, max_coincidence);

	D = "[N] -> { S_0[i, j] : i >= 1 and i <= N and j >= 1 and j <= N }";
	W = "[N] -> { S_0[i, j] -> s[0] : i >= 1 and i <= N and j >= 1 and "
					"j <= N }";
	R = "[N] -> { S_0[i, j] -> s[0] : i >= 1 and i <= N and j >= 1 and "
					"j <= N; "
		    "S_0[i, j] -> a[i, j] : i >= 1 and i <= N and j >= 1 and "
					"j <= N }";
	S = "[N] -> { S_0[i, j] -> [0, i, 0, j, 0] }";
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;

	D = "[N] -> { S_0[t] : t >= 0 and t <= -1 + N; "
		    " S_2[t] : t >= 0 and t <= -1 + N; "
		    " S_1[t, i] : t >= 0 and t <= -1 + N and i >= 0 and "
				"i <= -1 + N }";
	W = "[N] -> { S_0[t] -> a[t, 0] : t >= 0 and t <= -1 + N; "
		    " S_2[t] -> b[t] : t >= 0 and t <= -1 + N; "
		    " S_1[t, i] -> a[t, 1 + i] : t >= 0 and t <= -1 + N and "
						"i >= 0 and i <= -1 + N }";
	R = "[N] -> { S_1[t, i] -> a[t, i] : t >= 0 and t <= -1 + N and "
					    "i >= 0 and i <= -1 + N; "
		    " S_2[t] -> a[t, N] : t >= 0 and t <= -1 + N }";
	S = "[N] -> { S_2[t] -> [0, t, 2]; S_1[t, i] -> [0, t, 1, i, 0]; "
		    " S_0[t] -> [0, t, 0] }";

	if (test_one_schedule(ctx, D, W, R, S, 2, 1) < 0)
		return -1;
	ctx->opt->schedule_parametric = 0;
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;
	ctx->opt->schedule_parametric = 1;

	D = "[N] -> { S1[i,j] : 0 <= i,j < N; S2[i,j] : 0 <= i,j < N }";
	S = "{ S1[i,j] -> [0,i,j]; S2[i,j] -> [1,i,j] }";
	if (test_one_schedule(ctx, D, "{}", "{}", S, 2, 2) < 0)
		return -1;

	D = "[M, N] -> { S_1[i] : i >= 0 and i <= -1 + M; "
	    "S_0[i, j] : i >= 0 and i <= -1 + M and j >= 0 and j <= -1 + N }";
	W = "[M, N] -> { S_0[i, j] -> a[j] : i >= 0 and i <= -1 + M and "
					    "j >= 0 and j <= -1 + N; "
			"S_1[i] -> b[0] : i >= 0 and i <= -1 + M }";
	R = "[M, N] -> { S_0[i, j] -> a[0] : i >= 0 and i <= -1 + M and "
					    "j >= 0 and j <= -1 + N; "
			"S_1[i] -> b[0] : i >= 0 and i <= -1 + M }";
	S = "[M, N] -> { S_1[i] -> [1, i, 0]; S_0[i, j] -> [0, i, 0, j, 0] }";
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;

	D = "{ S_0[i] : i >= 0 }";
	W = "{ S_0[i] -> a[i] : i >= 0 }";
	R = "{ S_0[i] -> a[0] : i >= 0 }";
	S = "{ S_0[i] -> [0, i, 0] }";
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;

	D = "{ S_0[i] : i >= 0; S_1[i] : i >= 0 }";
	W = "{ S_0[i] -> a[i] : i >= 0; S_1[i] -> b[i] : i >= 0 }";
	R = "{ S_0[i] -> b[0] : i >= 0; S_1[i] -> a[i] : i >= 0 }";
	S = "{ S_1[i] -> [0, i, 1]; S_0[i] -> [0, i, 0] }";
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;

	D = "[n] -> { S_0[j, k] : j <= -1 + n and j >= 0 and "
				"k <= -1 + n and k >= 0 }";
	W = "[n] -> { S_0[j, k] -> B[j] : j <= -1 + n and j >= 0 and "							"k <= -1 + n and k >= 0 }";
	R = "[n] -> { S_0[j, k] -> B[j] : j <= -1 + n and j >= 0 and "
					"k <= -1 + n and k >= 0; "
		    "S_0[j, k] -> B[k] : j <= -1 + n and j >= 0 and "
					"k <= -1 + n and k >= 0; "
		    "S_0[j, k] -> A[k] : j <= -1 + n and j >= 0 and "
					"k <= -1 + n and k >= 0 }";
	S = "[n] -> { S_0[j, k] -> [2, j, k] }";
	ctx->opt->schedule_outer_coincidence = 1;
	if (test_one_schedule(ctx, D, W, R, S, 0, 0) < 0)
		return -1;
	ctx->opt->schedule_outer_coincidence = 0;

	D = "{Stmt_for_body24[i0, i1, i2, i3]:"
		"i0 >= 0 and i0 <= 1 and i1 >= 0 and i1 <= 6 and i2 >= 2 and "
		"i2 <= 6 - i1 and i3 >= 0 and i3 <= -1 + i2;"
	     "Stmt_for_body24[i0, i1, 1, 0]:"
		"i0 >= 0 and i0 <= 1 and i1 >= 0 and i1 <= 5;"
	     "Stmt_for_body7[i0, i1, i2]:"
		"i0 >= 0 and i0 <= 1 and i1 >= 0 and i1 <= 7 and i2 >= 0 and "
		"i2 <= 7 }";

	V = "{Stmt_for_body24[0, i1, i2, i3] -> "
		"Stmt_for_body24[1, i1, i2, i3]:"
		"i3 >= 0 and i3 <= -1 + i2 and i1 >= 0 and i2 <= 6 - i1 and "
		"i2 >= 1;"
	     "Stmt_for_body24[0, i1, i2, i3] -> "
		"Stmt_for_body7[1, 1 + i1 + i3, 1 + i1 + i2]:"
		"i3 <= -1 + i2 and i2 <= 6 - i1 and i2 >= 1 and i1 >= 0 and "
		"i3 >= 0;"
	      "Stmt_for_body24[0, i1, i2, i3] ->"
		"Stmt_for_body7[1, i1, 1 + i1 + i3]:"
		"i3 >= 0 and i2 <= 6 - i1 and i1 >= 0 and i3 <= -1 + i2;"
	      "Stmt_for_body7[0, i1, i2] -> Stmt_for_body7[1, i1, i2]:"
		"(i2 >= 1 + i1 and i2 <= 6 and i1 >= 0 and i1 <= 4) or "
		"(i2 >= 3 and i2 <= 7 and i1 >= 1 and i2 >= 1 + i1) or "
		"(i2 >= 0 and i2 <= i1 and i2 >= -7 + i1 and i1 <= 7);"
	      "Stmt_for_body7[0, i1, 1 + i1] -> Stmt_for_body7[1, i1, 1 + i1]:"
		"i1 <= 6 and i1 >= 0;"
	      "Stmt_for_body7[0, 0, 7] -> Stmt_for_body7[1, 0, 7];"
	      "Stmt_for_body7[i0, i1, i2] -> "
		"Stmt_for_body24[i0, o1, -1 + i2 - o1, -1 + i1 - o1]:"
		"i0 >= 0 and i0 <= 1 and o1 >= 0 and i2 >= 1 + i1 and "
		"o1 <= -2 + i2 and i2 <= 7 and o1 <= -1 + i1;"
	      "Stmt_for_body7[i0, i1, i2] -> "
		"Stmt_for_body24[i0, i1, o2, -1 - i1 + i2]:"
		"i0 >= 0 and i0 <= 1 and i1 >= 0 and o2 >= -i1 + i2 and "
		"o2 >= 1 and o2 <= 6 - i1 and i2 >= 1 + i1 }";
	P = V;

	treat_coalescing = isl_options_get_schedule_treat_coalescing(ctx);
	isl_options_set_schedule_treat_coalescing(ctx, 0);
	if (test_has_schedule(ctx, D, V, P) < 0)
		return -1;
	isl_options_set_schedule_treat_coalescing(ctx, treat_coalescing);

	D = "{ S_0[i, j] : i >= 1 and i <= 10 and j >= 1 and j <= 8 }";
	V = "{ S_0[i, j] -> S_0[i, 1 + j] : i >= 1 and i <= 10 and "
					   "j >= 1 and j <= 7;"
		"S_0[i, j] -> S_0[1 + i, j] : i >= 1 and i <= 9 and "
					     "j >= 1 and j <= 8 }";
	P = "{ }";
	S = "{ S_0[i, j] -> [i + j, i] }";
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_FEAUTRIER;
	if (test_special_schedule(ctx, D, V, P, S) < 0)
		return -1;
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_ISL;

	/* Fig. 1 from Feautrier's "Some Efficient Solutions..." pt. 2, 1992 */
	D = "[N] -> { S_0[i, j] : i >= 0 and i <= -1 + N and "
				 "j >= 0 and j <= -1 + i }";
	V = "[N] -> { S_0[i, j] -> S_0[i, 1 + j] : j <= -2 + i and "
					"i <= -1 + N and j >= 0;"
		     "S_0[i, -1 + i] -> S_0[1 + i, 0] : i >= 1 and "
					"i <= -2 + N }";
	P = "{ }";
	S = "{ S_0[i, j] -> [i, j] }";
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_FEAUTRIER;
	if (test_special_schedule(ctx, D, V, P, S) < 0)
		return -1;
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_ISL;

	/* Test both algorithms on a case with only proximity dependences. */
	D = "{ S[i,j] : 0 <= i <= 10 }";
	V = "{ }";
	P = "{ S[i,j] -> S[i+1,j] : 0 <= i,j <= 10 }";
	S = "{ S[i, j] -> [j, i] }";
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_FEAUTRIER;
	if (test_special_schedule(ctx, D, V, P, S) < 0)
		return -1;
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_ISL;
	if (test_special_schedule(ctx, D, V, P, S) < 0)
		return -1;
	
	D = "{ A[a]; B[] }";
	V = "{}";
	P = "{ A[a] -> B[] }";
	if (test_has_schedule(ctx, D, V, P) < 0)
		return -1;

	if (test_padded_schedule(ctx) < 0)
		return -1;

	/* Check that check for progress is not confused by rational
	 * solution.
	 */
	D = "[N] -> { S0[i, j] : i >= 0 and i <= N and j >= 0 and j <= N }";
	V = "[N] -> { S0[i0, -1 + N] -> S0[2 + i0, 0] : i0 >= 0 and "
							"i0 <= -2 + N; "
			"S0[i0, i1] -> S0[i0, 1 + i1] : i0 >= 0 and "
				"i0 <= N and i1 >= 0 and i1 <= -1 + N }";
	P = "{}";
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_FEAUTRIER;
	if (test_has_schedule(ctx, D, V, P) < 0)
		return -1;
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_ISL;

	/* Check that we allow schedule rows that are only non-trivial
	 * on some full-dimensional domains.
	 */
	D = "{ S1[j] : 0 <= j <= 1; S0[]; S2[k] : 0 <= k <= 1 }";
	V = "{ S0[] -> S1[j] : 0 <= j <= 1; S2[0] -> S0[];"
		"S1[j] -> S2[1] : 0 <= j <= 1 }";
	P = "{}";
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_FEAUTRIER;
	if (test_has_schedule(ctx, D, V, P) < 0)
		return -1;
	ctx->opt->schedule_algorithm = ISL_SCHEDULE_ALGORITHM_ISL;

	if (test_conditional_schedule_constraints(ctx) < 0)
		return -1;

	if (test_strongly_satisfying_schedule(ctx) < 0)
		return -1;

	if (test_conflicting_context_schedule(ctx) < 0)
		return -1;

	if (test_coalescing_schedule(ctx) < 0)
		return -1;
	if (test_skewing_schedule(ctx) < 0)
		return -1;

	return 0;
}

/* Perform scheduling tests using the whole component scheduler.
 */
static int test_schedule_whole(isl_ctx *ctx)
{
	int whole;
	int r;

	whole = isl_options_get_schedule_whole_component(ctx);
	isl_options_set_schedule_whole_component(ctx, 1);
	r = test_schedule(ctx);
	isl_options_set_schedule_whole_component(ctx, whole);

	return r;
}

/* Perform scheduling tests using the incremental scheduler.
 */
static int test_schedule_incremental(isl_ctx *ctx)
{
	int whole;
	int r;

	whole = isl_options_get_schedule_whole_component(ctx);
	isl_options_set_schedule_whole_component(ctx, 0);
	r = test_schedule(ctx);
	isl_options_set_schedule_whole_component(ctx, whole);

	return r;
}

struct {
	const char *name;
	int (*fn)(isl_ctx *ctx);
} tests [] = {
	{ "schedule (whole component)", &test_schedule_whole },
	{ "schedule (incremental)", &test_schedule_incremental },
};

int main(int argc, char **argv)
{
	int i;
	struct isl_ctx *ctx;
	struct isl_options *options;

	options = isl_options_new_with_defaults();
	assert(options);
	argc = isl_options_parse(options, argc, argv, ISL_ARG_ALL);

	ctx = isl_ctx_alloc_with_options(&isl_options_args, options);
	for (i = 0; i < ARRAY_SIZE(tests); ++i) {
		printf("%s\n", tests[i].name);
		if (tests[i].fn(ctx) < 0)
			goto error;
	}
	isl_ctx_free(ctx);
	return 0;
error:
	isl_ctx_free(ctx);
	return -1;
}
