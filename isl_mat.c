#include "isl_dim.h"
#include "isl_seq.h"
#include "isl_mat.h"
#include "isl_map_private.h"

struct isl_mat *isl_mat_alloc(struct isl_ctx *ctx,
	unsigned n_row, unsigned n_col)
{
	int i;
	struct isl_mat *mat;

	mat = isl_alloc_type(ctx, struct isl_mat);
	if (!mat)
		return NULL;

	mat->row = NULL;
	mat->block = isl_blk_alloc(ctx, n_row * n_col);
	if (isl_blk_is_error(mat->block))
		goto error;
	mat->row = isl_alloc_array(ctx, isl_int *, n_row);
	if (!mat->row)
		goto error;

	for (i = 0; i < n_row; ++i)
		mat->row[i] = mat->block.data + i * n_col;

	mat->ref = 1;
	mat->n_row = n_row;
	mat->n_col = n_col;
	mat->flags = 0;

	return mat;
error:
	isl_blk_free(ctx, mat->block);
	free(mat);
	return NULL;
}

struct isl_mat *isl_mat_extend(struct isl_ctx *ctx, struct isl_mat *mat,
	unsigned n_row, unsigned n_col)
{
	int i;

	if (!mat)
		return NULL;

	if (mat->n_col >= n_col && mat->n_row >= n_row)
		return mat;

	if (mat->n_col < n_col) {
		struct isl_mat *new_mat;

		new_mat = isl_mat_alloc(ctx, n_row, n_col);
		if (!new_mat)
			goto error;
		for (i = 0; i < mat->n_row; ++i)
			isl_seq_cpy(new_mat->row[i], mat->row[i], mat->n_col);
		isl_mat_free(ctx, mat);
		return new_mat;
	}

	mat = isl_mat_cow(ctx, mat);
	if (!mat)
		goto error;

	assert(mat->ref == 1);
	mat->block = isl_blk_extend(ctx, mat->block, n_row * mat->n_col);
	if (isl_blk_is_error(mat->block))
		goto error;
	mat->row = isl_realloc_array(ctx, mat->row, isl_int *, n_row);
	if (!mat->row)
		goto error;

	for (i = 0; i < n_row; ++i)
		mat->row[i] = mat->block.data + i * mat->n_col;
	mat->n_row = n_row;

	return mat;
error:
	isl_mat_free(ctx, mat);
	return NULL;
}

struct isl_mat *isl_mat_sub_alloc(struct isl_ctx *ctx, isl_int **row,
	unsigned first_row, unsigned n_row, unsigned first_col, unsigned n_col)
{
	int i;
	struct isl_mat *mat;

	mat = isl_alloc_type(ctx, struct isl_mat);
	if (!mat)
		return NULL;
	mat->row = isl_alloc_array(ctx, isl_int *, n_row);
	if (!mat->row)
		goto error;
	for (i = 0; i < n_row; ++i)
		mat->row[i] = row[first_row+i] + first_col;
	mat->ref = 1;
	mat->n_row = n_row;
	mat->n_col = n_col;
	mat->block = isl_blk_empty();
	mat->flags = ISL_MAT_BORROWED;
	return mat;
error:
	free(mat);
	return NULL;
}

void isl_mat_sub_copy(struct isl_ctx *ctx, isl_int **dst, isl_int **src,
	unsigned n_row, unsigned dst_col, unsigned src_col, unsigned n_col)
{
	int i;

	for (i = 0; i < n_row; ++i)
		isl_seq_cpy(dst[i]+dst_col, src[i]+src_col, n_col);
}

void isl_mat_sub_neg(struct isl_ctx *ctx, isl_int **dst, isl_int **src,
	unsigned n_row, unsigned dst_col, unsigned src_col, unsigned n_col)
{
	int i;

	for (i = 0; i < n_row; ++i)
		isl_seq_neg(dst[i]+dst_col, src[i]+src_col, n_col);
}

struct isl_mat *isl_mat_copy(struct isl_ctx *ctx, struct isl_mat *mat)
{
	if (!mat)
		return NULL;

	mat->ref++;
	return mat;
}

struct isl_mat *isl_mat_dup(struct isl_ctx *ctx, struct isl_mat *mat)
{
	int i;
	struct isl_mat *mat2;

	if (!mat)
		return NULL;
	mat2 = isl_mat_alloc(ctx, mat->n_row, mat->n_col);
	if (!mat2)
		return NULL;
	for (i = 0; i < mat->n_row; ++i)
		isl_seq_cpy(mat2->row[i], mat->row[i], mat->n_col);
	return mat2;
}

struct isl_mat *isl_mat_cow(struct isl_ctx *ctx, struct isl_mat *mat)
{
	struct isl_mat *mat2;
	if (!mat)
		return NULL;

	if (mat->ref == 1 && !ISL_F_ISSET(mat, ISL_MAT_BORROWED))
		return mat;

	mat2 = isl_mat_dup(ctx, mat);
	isl_mat_free(ctx, mat);
	return mat2;
}

void isl_mat_free(struct isl_ctx *ctx, struct isl_mat *mat)
{
	if (!mat)
		return;

	if (--mat->ref > 0)
		return;

	if (!ISL_F_ISSET(mat, ISL_MAT_BORROWED))
		isl_blk_free(ctx, mat->block);
	free(mat->row);
	free(mat);
}

struct isl_mat *isl_mat_identity(struct isl_ctx *ctx, unsigned n_row)
{
	int i;
	struct isl_mat *mat;

	mat = isl_mat_alloc(ctx, n_row, n_row);
	if (!mat)
		return NULL;
	for (i = 0; i < n_row; ++i) {
		isl_seq_clr(mat->row[i], i);
		isl_int_set_si(mat->row[i][i], 1);
		isl_seq_clr(mat->row[i]+i+1, n_row-(i+1));
	}

	return mat;
}

struct isl_vec *isl_mat_vec_product(struct isl_ctx *ctx,
	struct isl_mat *mat, struct isl_vec *vec)
{
	int i;
	struct isl_vec *prod;

	if (!mat || !vec)
		goto error;

	isl_assert(ctx, mat->n_col == vec->size, goto error);

	prod = isl_vec_alloc(ctx, mat->n_row);
	if (!prod)
		goto error;

	for (i = 0; i < prod->size; ++i)
		isl_seq_inner_product(mat->row[i], vec->block.data, vec->size,
					&prod->block.data[i]);
	isl_mat_free(ctx, mat);
	isl_vec_free(ctx, vec);
	return prod;
error:
	isl_mat_free(ctx, mat);
	isl_vec_free(ctx, vec);
	return NULL;
}

struct isl_mat *isl_mat_aff_direct_sum(struct isl_ctx *ctx,
	struct isl_mat *left, struct isl_mat *right)
{
	int i;
	struct isl_mat *sum;

	if (!left || !right)
		goto error;

	isl_assert(ctx, left->n_row == right->n_row, goto error);
	isl_assert(ctx, left->n_row >= 1, goto error);
	isl_assert(ctx, left->n_col >= 1, goto error);
	isl_assert(ctx, right->n_col >= 1, goto error);
	isl_assert(ctx,
	    isl_seq_first_non_zero(left->row[0]+1, left->n_col-1) == -1,
	    goto error);
	isl_assert(ctx,
	    isl_seq_first_non_zero(right->row[0]+1, right->n_col-1) == -1,
	    goto error);

	sum = isl_mat_alloc(ctx, left->n_row, left->n_col + right->n_col - 1);
	if (!sum)
		goto error;
	isl_int_lcm(sum->row[0][0], left->row[0][0], right->row[0][0]);
	isl_int_divexact(left->row[0][0], sum->row[0][0], left->row[0][0]);
	isl_int_divexact(right->row[0][0], sum->row[0][0], right->row[0][0]);

	isl_seq_clr(sum->row[0]+1, sum->n_col-1);
	for (i = 1; i < sum->n_row; ++i) {
		isl_int_mul(sum->row[i][0], left->row[0][0], left->row[i][0]);
		isl_int_addmul(sum->row[i][0],
				right->row[0][0], right->row[i][0]);
		isl_seq_scale(sum->row[i]+1, left->row[i]+1, left->row[0][0],
				left->n_col-1);
		isl_seq_scale(sum->row[i]+left->n_col,
				right->row[i]+1, right->row[0][0],
				right->n_col-1);
	}

	isl_int_divexact(left->row[0][0], sum->row[0][0], left->row[0][0]);
	isl_int_divexact(right->row[0][0], sum->row[0][0], right->row[0][0]);
	isl_mat_free(ctx, left);
	isl_mat_free(ctx, right);
	return sum;
error:
	isl_mat_free(ctx, left);
	isl_mat_free(ctx, right);
	return NULL;
}

static void exchange(struct isl_ctx *ctx, struct isl_mat *M, struct isl_mat **U,
	struct isl_mat **Q, unsigned row, unsigned i, unsigned j)
{
	int r;
	for (r = row; r < M->n_row; ++r)
		isl_int_swap(M->row[r][i], M->row[r][j]);
	if (U) {
		for (r = 0; r < (*U)->n_row; ++r)
			isl_int_swap((*U)->row[r][i], (*U)->row[r][j]);
	}
	if (Q)
		isl_mat_swap_rows(ctx, *Q, i, j);
}

static void subtract(struct isl_mat *M, struct isl_mat **U,
	struct isl_mat **Q, unsigned row, unsigned i, unsigned j, isl_int m)
{
	int r;
	for (r = row; r < M->n_row; ++r)
		isl_int_submul(M->row[r][j], m, M->row[r][i]);
	if (U) {
		for (r = 0; r < (*U)->n_row; ++r)
			isl_int_submul((*U)->row[r][j], m, (*U)->row[r][i]);
	}
	if (Q) {
		for (r = 0; r < (*Q)->n_col; ++r)
			isl_int_addmul((*Q)->row[i][r], m, (*Q)->row[j][r]);
	}
}

static void oppose(struct isl_ctx *ctx, struct isl_mat *M, struct isl_mat **U,
	struct isl_mat **Q, unsigned row, unsigned col)
{
	int r;
	for (r = row; r < M->n_row; ++r)
		isl_int_neg(M->row[r][col], M->row[r][col]);
	if (U) {
		for (r = 0; r < (*U)->n_row; ++r)
			isl_int_neg((*U)->row[r][col], (*U)->row[r][col]);
	}
	if (Q)
		isl_seq_neg((*Q)->row[col], (*Q)->row[col], (*Q)->n_col);
}

/* Given matrix M, compute
 *
 *		M U = H
 *		M   = H Q
 *
 * with U and Q unimodular matrices and H a matrix in column echelon form
 * such that on each echelon row the entries in the non-echelon column
 * are non-negative (if neg == 0) or non-positive (if neg == 1)
 * and stricly smaller (in absolute value) than the entries in the echelon
 * column.
 * If U or Q are NULL, then these matrices are not computed.
 */
struct isl_mat *isl_mat_left_hermite(struct isl_ctx *ctx,
	struct isl_mat *M, int neg, struct isl_mat **U, struct isl_mat **Q)
{
	isl_int c;
	int row, col;

	if (U)
		*U = NULL;
	if (Q)
		*Q = NULL;
	if (!M)
		goto error;
	M = isl_mat_cow(ctx, M);
	if (!M)
		goto error;
	if (U) {
		*U = isl_mat_identity(ctx, M->n_col);
		if (!*U)
			goto error;
	}
	if (Q) {
		*Q = isl_mat_identity(ctx, M->n_col);
		if (!*Q)
			goto error;
	}

	col = 0;
	isl_int_init(c);
	for (row = 0; row < M->n_row; ++row) {
		int first, i, off;
		first = isl_seq_abs_min_non_zero(M->row[row]+col, M->n_col-col);
		if (first == -1)
			continue;
		first += col;
		if (first != col)
			exchange(ctx, M, U, Q, row, first, col);
		if (isl_int_is_neg(M->row[row][col]))
			oppose(ctx, M, U, Q, row, col);
		first = col+1;
		while ((off = isl_seq_first_non_zero(M->row[row]+first,
						       M->n_col-first)) != -1) {
			first += off;
			isl_int_fdiv_q(c, M->row[row][first], M->row[row][col]);
			subtract(M, U, Q, row, col, first, c);
			if (!isl_int_is_zero(M->row[row][first]))
				exchange(ctx, M, U, Q, row, first, col);
			else
				++first;
		}
		for (i = 0; i < col; ++i) {
			if (isl_int_is_zero(M->row[row][i]))
				continue;
			if (neg)
				isl_int_cdiv_q(c, M->row[row][i], M->row[row][col]);
			else
				isl_int_fdiv_q(c, M->row[row][i], M->row[row][col]);
			if (isl_int_is_zero(c))
				continue;
			subtract(M, U, Q, row, col, i, c);
		}
		++col;
	}
	isl_int_clear(c);

	return M;
error:
	if (Q) {
		isl_mat_free(ctx, *Q);
		*Q = NULL;
	}
	if (U) {
		isl_mat_free(ctx, *U);
		*U = NULL;
	}
	return NULL;
}

struct isl_mat *isl_mat_right_kernel(struct isl_ctx *ctx, struct isl_mat *mat)
{
	int i, rank;
	struct isl_mat *U = NULL;
	struct isl_mat *K;

	mat = isl_mat_left_hermite(ctx, mat, 0, &U, NULL);
	if (!mat || !U)
		goto error;

	for (i = 0, rank = 0; rank < mat->n_col; ++rank) {
		while (i < mat->n_row && isl_int_is_zero(mat->row[i][rank]))
			++i;
		if (i >= mat->n_row)
			break;
	}
	K = isl_mat_alloc(ctx, U->n_row, U->n_col - rank);
	if (!K)
		goto error;
	isl_mat_sub_copy(ctx, K->row, U->row, U->n_row, 0, rank, U->n_col-rank);
	isl_mat_free(ctx, mat);
	isl_mat_free(ctx, U);
	return K;
error:
	isl_mat_free(ctx, mat);
	isl_mat_free(ctx, U);
	return NULL;
}

struct isl_mat *isl_mat_lin_to_aff(struct isl_ctx *ctx, struct isl_mat *mat)
{
	int i;
	struct isl_mat *mat2;

	if (!mat)
		return NULL;
	mat2 = isl_mat_alloc(ctx, 1+mat->n_row, 1+mat->n_col);
	if (!mat2)
		return NULL;
	isl_int_set_si(mat2->row[0][0], 1);
	isl_seq_clr(mat2->row[0]+1, mat->n_col);
	for (i = 0; i < mat->n_row; ++i) {
		isl_int_set_si(mat2->row[1+i][0], 0);
		isl_seq_cpy(mat2->row[1+i]+1, mat->row[i], mat->n_col);
	}
	isl_mat_free(ctx, mat);
	return mat2;
}

static int row_first_non_zero(isl_int **row, unsigned n_row, unsigned col)
{
	int i;

	for (i = 0; i < n_row; ++i)
		if (!isl_int_is_zero(row[i][col]))
			return i;
	return -1;
}

static int row_abs_min_non_zero(isl_int **row, unsigned n_row, unsigned col)
{
	int i, min = row_first_non_zero(row, n_row, col);
	if (min < 0)
		return -1;
	for (i = min + 1; i < n_row; ++i) {
		if (isl_int_is_zero(row[i][col]))
			continue;
		if (isl_int_abs_lt(row[i][col], row[min][col]))
			min = i;
	}
	return min;
}

static void inv_exchange(struct isl_ctx *ctx,
	struct isl_mat *left, struct isl_mat *right,
	unsigned i, unsigned j)
{
	left = isl_mat_swap_rows(ctx, left, i, j);
	right = isl_mat_swap_rows(ctx, right, i, j);
}

static void inv_oppose(struct isl_ctx *ctx,
	struct isl_mat *left, struct isl_mat *right, unsigned row)
{
	isl_seq_neg(left->row[row]+row, left->row[row]+row, left->n_col-row);
	isl_seq_neg(right->row[row], right->row[row], right->n_col);
}

static void inv_subtract(struct isl_ctx *ctx,
	struct isl_mat *left, struct isl_mat *right,
	unsigned row, unsigned i, isl_int m)
{
	isl_int_neg(m, m);
	isl_seq_combine(left->row[i]+row,
			ctx->one, left->row[i]+row,
			m, left->row[row]+row,
			left->n_col-row);
	isl_seq_combine(right->row[i], ctx->one, right->row[i],
			m, right->row[row], right->n_col);
}

/* Compute inv(left)*right
 */
struct isl_mat *isl_mat_inverse_product(struct isl_ctx *ctx,
	struct isl_mat *left, struct isl_mat *right)
{
	int row;
	isl_int a, b;

	if (!left || !right)
		goto error;

	isl_assert(ctx, left->n_row == left->n_col, goto error);
	isl_assert(ctx, left->n_row == right->n_row, goto error);

	if (left->n_row == 0) {
		isl_mat_free(ctx, left);
		return right;
	}

	left = isl_mat_cow(ctx, left);
	right = isl_mat_cow(ctx, right);
	if (!left || !right)
		goto error;

	isl_int_init(a);
	isl_int_init(b);
	for (row = 0; row < left->n_row; ++row) {
		int pivot, first, i, off;
		pivot = row_abs_min_non_zero(left->row+row, left->n_row-row, row);
		if (pivot < 0) {
			isl_int_clear(a);
			isl_int_clear(b);
			isl_assert(ctx, pivot >= 0, goto error);
		}
		pivot += row;
		if (pivot != row)
			inv_exchange(ctx, left, right, pivot, row);
		if (isl_int_is_neg(left->row[row][row]))
			inv_oppose(ctx, left, right, row);
		first = row+1;
		while ((off = row_first_non_zero(left->row+first,
					left->n_row-first, row)) != -1) {
			first += off;
			isl_int_fdiv_q(a, left->row[first][row],
					left->row[row][row]);
			inv_subtract(ctx, left, right, row, first, a);
			if (!isl_int_is_zero(left->row[first][row]))
				inv_exchange(ctx, left, right, row, first);
			else
				++first;
		}
		for (i = 0; i < row; ++i) {
			if (isl_int_is_zero(left->row[i][row]))
				continue;
			isl_int_gcd(a, left->row[row][row], left->row[i][row]);
			isl_int_divexact(b, left->row[i][row], a);
			isl_int_divexact(a, left->row[row][row], a);
			isl_int_neg(a, a);
			isl_seq_combine(left->row[i]+row,
					a, left->row[i]+row,
					b, left->row[row]+row,
					left->n_col-row);
			isl_seq_combine(right->row[i], a, right->row[i],
					b, right->row[row], right->n_col);
		}
	}
	isl_int_clear(b);

	isl_int_set(a, left->row[0][0]);
	for (row = 1; row < left->n_row; ++row)
		isl_int_lcm(a, a, left->row[row][row]);
	if (isl_int_is_zero(a)){
		isl_int_clear(a);
		isl_assert(ctx, 0, goto error);
	}
	for (row = 0; row < left->n_row; ++row) {
		isl_int_divexact(left->row[row][row], a, left->row[row][row]);
		if (isl_int_is_one(left->row[row][row]))
			continue;
		isl_seq_scale(right->row[row], right->row[row],
				left->row[row][row], right->n_col);
	}
	isl_int_clear(a);

	isl_mat_free(ctx, left);
	return right;
error:
	isl_mat_free(ctx, left);
	isl_mat_free(ctx, right);
	return NULL;
}

void isl_mat_col_scale(struct isl_mat *mat, unsigned col, isl_int m)
{
	int i;

	for (i = 0; i < mat->n_row; ++i)
		isl_int_mul(mat->row[i][col], mat->row[i][col], m);
}

void isl_mat_col_combine(struct isl_mat *mat, unsigned dst,
	isl_int m1, unsigned src1, isl_int m2, unsigned src2)
{
	int i;
	isl_int tmp;

	isl_int_init(tmp);
	for (i = 0; i < mat->n_row; ++i) {
		isl_int_mul(tmp, m1, mat->row[i][src1]);
		isl_int_addmul(tmp, m2, mat->row[i][src2]);
		isl_int_set(mat->row[i][dst], tmp);
	}
	isl_int_clear(tmp);
}

struct isl_mat *isl_mat_right_inverse(struct isl_ctx *ctx,
	struct isl_mat *mat)
{
	struct isl_mat *inv;
	int row;
	isl_int a, b;

	mat = isl_mat_cow(ctx, mat);
	if (!mat)
		return NULL;

	inv = isl_mat_identity(ctx, mat->n_col);
	inv = isl_mat_cow(ctx, inv);
	if (!inv)
		goto error;

	isl_int_init(a);
	isl_int_init(b);
	for (row = 0; row < mat->n_row; ++row) {
		int pivot, first, i, off;
		pivot = isl_seq_abs_min_non_zero(mat->row[row]+row, mat->n_col-row);
		if (pivot < 0) {
			isl_int_clear(a);
			isl_int_clear(b);
			goto error;
		}
		pivot += row;
		if (pivot != row)
			exchange(ctx, mat, &inv, NULL, row, pivot, row);
		if (isl_int_is_neg(mat->row[row][row]))
			oppose(ctx, mat, &inv, NULL, row, row);
		first = row+1;
		while ((off = isl_seq_first_non_zero(mat->row[row]+first,
						    mat->n_col-first)) != -1) {
			first += off;
			isl_int_fdiv_q(a, mat->row[row][first],
						    mat->row[row][row]);
			subtract(mat, &inv, NULL, row, row, first, a);
			if (!isl_int_is_zero(mat->row[row][first]))
				exchange(ctx, mat, &inv, NULL, row, row, first);
			else
				++first;
		}
		for (i = 0; i < row; ++i) {
			if (isl_int_is_zero(mat->row[row][i]))
				continue;
			isl_int_gcd(a, mat->row[row][row], mat->row[row][i]);
			isl_int_divexact(b, mat->row[row][i], a);
			isl_int_divexact(a, mat->row[row][row], a);
			isl_int_neg(a, a);
			isl_mat_col_combine(mat, i, a, i, b, row);
			isl_mat_col_combine(inv, i, a, i, b, row);
		}
	}
	isl_int_clear(b);

	isl_int_set(a, mat->row[0][0]);
	for (row = 1; row < mat->n_row; ++row)
		isl_int_lcm(a, a, mat->row[row][row]);
	if (isl_int_is_zero(a)){
		isl_int_clear(a);
		goto error;
	}
	for (row = 0; row < mat->n_row; ++row) {
		isl_int_divexact(mat->row[row][row], a, mat->row[row][row]);
		if (isl_int_is_one(mat->row[row][row]))
			continue;
		isl_mat_col_scale(inv, row, mat->row[row][row]);
	}
	isl_int_clear(a);

	isl_mat_free(ctx, mat);

	return inv;
error:
	isl_mat_free(ctx, mat);
	return NULL;
}

struct isl_mat *isl_mat_transpose(struct isl_ctx *ctx, struct isl_mat *mat)
{
	struct isl_mat *transpose = NULL;
	int i, j;

	if (mat->n_col == mat->n_row) {
		mat = isl_mat_cow(ctx, mat);
		if (!mat)
			return NULL;
		for (i = 0; i < mat->n_row; ++i)
			for (j = i + 1; j < mat->n_col; ++j)
				isl_int_swap(mat->row[i][j], mat->row[j][i]);
		return mat;
	}
	transpose = isl_mat_alloc(ctx, mat->n_col, mat->n_row);
	if (!transpose)
		goto error;
	for (i = 0; i < mat->n_row; ++i)
		for (j = 0; j < mat->n_col; ++j)
			isl_int_set(transpose->row[j][i], mat->row[i][j]);
	isl_mat_free(ctx, mat);
	return transpose;
error:
	isl_mat_free(ctx, mat);
	return NULL;
}

struct isl_mat *isl_mat_swap_cols(struct isl_ctx *ctx,
	struct isl_mat *mat, unsigned i, unsigned j)
{
	int r;

	mat = isl_mat_cow(ctx, mat);
	if (!mat)
		return NULL;
	isl_assert(ctx, i < mat->n_col, goto error);
	isl_assert(ctx, j < mat->n_col, goto error);

	for (r = 0; r < mat->n_row; ++r)
		isl_int_swap(mat->row[r][i], mat->row[r][j]);
	return mat;
error:
	isl_mat_free(ctx, mat);
	return NULL;
}

struct isl_mat *isl_mat_swap_rows(struct isl_ctx *ctx,
	struct isl_mat *mat, unsigned i, unsigned j)
{
	isl_int *t;

	if (!mat)
		return NULL;
	mat = isl_mat_cow(ctx, mat);
	if (!mat)
		return NULL;
	t = mat->row[i];
	mat->row[i] = mat->row[j];
	mat->row[j] = t;
	return mat;
}

struct isl_mat *isl_mat_product(struct isl_ctx *ctx,
	struct isl_mat *left, struct isl_mat *right)
{
	int i, j, k;
	struct isl_mat *prod;

	if (!left || !right)
		goto error;
	isl_assert(ctx, left->n_col == right->n_row, goto error);
	prod = isl_mat_alloc(ctx, left->n_row, right->n_col);
	if (!prod)
		goto error;
	if (left->n_col == 0) {
		for (i = 0; i < prod->n_row; ++i)
			isl_seq_clr(prod->row[i], prod->n_col);
		return prod;
	}
	for (i = 0; i < prod->n_row; ++i) {
		for (j = 0; j < prod->n_col; ++j) {
			isl_int_mul(prod->row[i][j],
				    left->row[i][0], right->row[0][j]);
			for (k = 1; k < left->n_col; ++k)
				isl_int_addmul(prod->row[i][j],
					    left->row[i][k], right->row[k][j]);
		}
	}
	isl_mat_free(ctx, left);
	isl_mat_free(ctx, right);
	return prod;
error:
	isl_mat_free(ctx, left);
	isl_mat_free(ctx, right);
	return NULL;
}

/* Replace the variables x in bset by x' given by x = M x', with
 * M the matrix mat.
 *
 * If there are fewer variables x' then there are x, then we perform
 * the transformation in place, which that, in principle,
 * this frees up some extra variables as the number
 * of columns remains constant, but we would have to extend
 * the div array too as the number of rows in this array is assumed
 * to be equal to extra.
 */
struct isl_basic_set *isl_basic_set_preimage(struct isl_basic_set *bset,
	struct isl_mat *mat)
{
	struct isl_ctx *ctx;
	struct isl_mat *t;
	int i;

	if (!bset || !mat)
		goto error;

	ctx = bset->ctx;
	bset = isl_basic_set_cow(bset);
	if (!bset)
		goto error;

	isl_assert(ctx, bset->dim->nparam == 0, goto error);
	isl_assert(ctx, bset->n_div == 0, goto error);
	isl_assert(ctx, 1+bset->dim->n_out == mat->n_row, goto error);

	if (mat->n_col > mat->n_row)
		bset = isl_basic_set_extend(bset, 0, mat->n_col-1, 0,
						0, 0);
	else if (mat->n_col < mat->n_row) {
		bset->dim = isl_dim_cow(bset->dim);
		if (!bset->dim)
			goto error;
		bset->dim->n_out -= mat->n_row - mat->n_col;
	}

	t = isl_mat_sub_alloc(ctx, bset->eq, 0, bset->n_eq, 0, mat->n_row);
	t = isl_mat_product(ctx, t, isl_mat_copy(ctx, mat));
	if (!t)
		goto error;
	for (i = 0; i < bset->n_eq; ++i) {
		isl_seq_swp_or_cpy(bset->eq[i], t->row[i], t->n_col);
		isl_seq_clr(bset->eq[i]+t->n_col, bset->extra);
	}
	isl_mat_free(ctx, t);

	t = isl_mat_sub_alloc(ctx, bset->ineq, 0, bset->n_ineq, 0, mat->n_row);
	t = isl_mat_product(ctx, t, mat);
	if (!t)
		goto error2;
	for (i = 0; i < bset->n_ineq; ++i) {
		isl_seq_swp_or_cpy(bset->ineq[i], t->row[i], t->n_col);
		isl_seq_clr(bset->ineq[i]+t->n_col, bset->extra);
	}
	isl_mat_free(ctx, t);

	ISL_F_CLR(bset, ISL_BASIC_SET_NO_IMPLICIT);
	ISL_F_CLR(bset, ISL_BASIC_SET_NO_REDUNDANT);
	ISL_F_CLR(bset, ISL_BASIC_SET_NORMALIZED);
	ISL_F_CLR(bset, ISL_BASIC_SET_NORMALIZED_DIVS);
	ISL_F_CLR(bset, ISL_BASIC_SET_ALL_EQUALITIES);

	bset = isl_basic_set_simplify(bset);
	bset = isl_basic_set_finalize(bset);

	return bset;
error:
	isl_mat_free(ctx, mat);
error2:
	isl_basic_set_free(bset);
	return NULL;
}

struct isl_set *isl_set_preimage(struct isl_set *set, struct isl_mat *mat)
{
	struct isl_ctx *ctx;
	int i;

	set = isl_set_cow(set);
	if (!set)
		return NULL;

	ctx = set->ctx;
	for (i = 0; i < set->n; ++i) {
		set->p[i] = isl_basic_set_preimage(set->p[i],
						    isl_mat_copy(ctx, mat));
		if (!set->p[i])
			goto error;
	}
	if (mat->n_col != mat->n_row) {
		set->dim = isl_dim_cow(set->dim);
		if (!set->dim)
			goto error;
		set->dim->n_out += mat->n_col;
		set->dim->n_out -= mat->n_row;
	}
	isl_mat_free(ctx, mat);
	ISL_F_CLR(set, ISL_SET_NORMALIZED);
	return set;
error:
	isl_set_free(set);
	isl_mat_free(ctx, mat);
	return NULL;
}

void isl_mat_dump(struct isl_ctx *ctx, struct isl_mat *mat,
				FILE *out, int indent)
{
	int i, j;

	if (!mat) {
		fprintf(out, "%*snull mat\n", indent, "");
		return;
	}

	if (mat->n_row == 0)
		fprintf(out, "%*s[]\n", indent, "");

	for (i = 0; i < mat->n_row; ++i) {
		if (!i)
			fprintf(out, "%*s[[", indent, "");
		else
			fprintf(out, "%*s[", indent+1, "");
		for (j = 0; j < mat->n_col; ++j) {
			if (j)
			    fprintf(out, ",");
			isl_int_print(out, mat->row[i][j], 0);
		}
		if (i == mat->n_row-1)
			fprintf(out, "]]\n");
		else
			fprintf(out, "]\n");
	}
}

struct isl_mat *isl_mat_drop_cols(struct isl_ctx *ctx, struct isl_mat *mat,
				unsigned col, unsigned n)
{
	int r;

	mat = isl_mat_cow(ctx, mat);
	if (!mat)
		return NULL;

	if (col != mat->n_col-n) {
		for (r = 0; r < mat->n_row; ++r)
			isl_seq_cpy(mat->row[r]+col, mat->row[r]+col+n,
					mat->n_col - col - n);
	}
	mat->n_col -= n;
	return mat;
}

struct isl_mat *isl_mat_drop_rows(struct isl_ctx *ctx, struct isl_mat *mat,
				unsigned row, unsigned n)
{
	int r;

	mat = isl_mat_cow(ctx, mat);
	if (!mat)
		return NULL;

	for (r = row; r+n < mat->n_row; ++r)
		mat->row[r] = mat->row[r+n];

	mat->n_row -= n;
	return mat;
}

void isl_mat_col_submul(struct isl_mat *mat,
			int dst_col, isl_int f, int src_col)
{
	int i;

	for (i = 0; i < mat->n_row; ++i)
		isl_int_submul(mat->row[i][dst_col], f, mat->row[i][src_col]);
}

void isl_mat_col_mul(struct isl_mat *mat, int dst_col, isl_int f, int src_col)
{
	int i;

	for (i = 0; i < mat->n_row; ++i)
		isl_int_mul(mat->row[i][dst_col], f, mat->row[i][src_col]);
}
