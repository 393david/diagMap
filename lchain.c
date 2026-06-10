#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include "mmpriv.h"
#include "kalloc.h"
#include "krmq.h"

static int64_t mg_chain_bk_end(int32_t max_drop, const mm128_t *z, const int32_t *f, const int64_t *p, int32_t *t, int64_t k)
{
	int64_t i = z[k].y, end_i = -1, max_i = i;
	int32_t max_s = 0;
	if (i < 0 || t[i] != 0) {
		return i;
	}
	do {
		int32_t s;
		t[i] = 2;
		//fprintf(stderr, "current anchor index i: %d, score: %d, previous anchor: %d, max_score: %d\n", i, f[i], p[i], max_s);
		end_i = i = p[i];
		s = i < 0? z[k].x : (int32_t)z[k].x - f[i];
		if (s > max_s) {
			max_s = s;
			max_i = i;}
		else if (max_s - s > max_drop) {
			break;
		}
	} while (i >= 0 && t[i] == 0);
	for (i = z[k].y; i >= 0 && i != end_i; i = p[i]) // reset modified t[]
		t[i] = 0;
	return max_i;
}
int compare_chain_ref(const void* a, const void* b) {
    return (int)(((mm64_t_each_chain*)a)->pos_ref_start - ((mm64_t_each_chain*)b)->pos_ref_start);
}
int compare_chain_query(const void* a, const void* b) {
    return (int)(((mm64_t_each_chain*)a)->pos_query_start - ((mm64_t_each_chain*)b)->pos_query_start);
}
uint64_t *mg_chain_backtrack(void *km, int64_t n, const int32_t *f, const int64_t *p, int32_t *v, int32_t *t, int32_t min_cnt, int32_t min_sc, int32_t max_drop, int32_t *n_u_, int32_t *n_v_)
{
	mm128_t *z;
	uint64_t *u;
	int64_t i, k, n_z, n_v;
	int32_t n_u;

	*n_u_ = *n_v_ = 0;
	for (i = 0, n_z = 0; i < n; ++i) // precompute n_z
		if (f[i] >= min_sc) ++n_z;
	if (n_z == 0) return 0;
	z = Kmalloc(km, mm128_t, n_z);
	for (i = 0, k = 0; i < n; ++i) // populate z[]
		if (f[i] >= min_sc) z[k].x = f[i], z[k++].y = i;
	radix_sort_128x(z, z + n_z);

	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // precompute n_u
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				++n_v, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				++n_u;
			else n_v = n_v0;
		}
	}
	u = Kmalloc(km, uint64_t, n_u);
	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // populate u[]
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				v[n_v++] = i, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				u[n_u++] = (uint64_t)sc << 32 | (n_v - n_v0);
			else n_v = n_v0;
		}
	}
	kfree(km, z);
	assert(n_v < INT32_MAX);
	*n_u_ = n_u, *n_v_ = n_v;
	return u;
}

// mymymy combine 45-degree chain from high to low score
// each loop selects two chains that has the min distance
int combine_chain2(mm64_t_each_chain *chain_pos, int32_t num_chain, int32_t *f, int64_t *p, int64_t *next){
	// determine whether two chains should be connected
	int32_t connected, rechain = 0, manhattan, manhattan_min, i, min_distance_index, k, num_connected1, num_connected2, combined_k_in_left;
	int32_t i_ref_start, i_ref_end, i_query_start, i_query_end, k_ref_start, k_ref_end, k_query_start, k_query_end;
	int32_t gap_ref_start, gap_ref_end, gap_query_start, gap_query_end, max_start, min_end;
	int8_t *flag_chains = (int8_t *)malloc(num_chain * sizeof(int8_t)); // the flag for each chain, -1: combined, 1
	int32_t combined_index_left, combined_index_right;
	for(i = 0; i < num_chain; i++){
		flag_chains[i] = 0; // 0: not combined, 1 means has been conbined
	}
	while(1){
		num_connected1 = 0;
		num_connected2 = 0;
		// first check the number of chains that has been conneced, for checking exist the while loop
		for(i = 0; i < num_chain; i++){ 
			if(flag_chains[i] == 1){
				num_connected1 += 1;
			}			
		}		
		for(i = 0; i < num_chain; i++){
			if(flag_chains[i] == 1){ // 1: has been combined
				continue;
			}
			min_distance_index = -1;
			connected = 0;
			manhattan_min = INT32_MAX;
			i_ref_start   = chain_pos[i].pos_ref_start;
			i_ref_end     = chain_pos[i].pos_ref_end;
			i_query_start = chain_pos[i].pos_query_start;
			i_query_end   = chain_pos[i].pos_query_end;
			// first find the no-overlapping chain has the min manhattan distance with i-th chain
			for(k = 0; k < num_chain; k++){
				if(flag_chains[k] == -1){ // -1: has been combined
					continue;
				}
				if(k == i){
					continue;
				}
				k_ref_start   = chain_pos[k].pos_ref_start;
				k_ref_end     = chain_pos[k].pos_ref_end;
				k_query_start = chain_pos[k].pos_query_start;
				k_query_end   = chain_pos[k].pos_query_end;
				// first, left: the k-th chain, right: i-th chain in the anchor 2D plot 
				if (i_ref_start > k_ref_end && i_query_start > k_query_end){
					manhattan = i_ref_start - k_ref_end + i_query_start - k_query_end;
					if(manhattan < manhattan_min){
						manhattan_min = manhattan;
						min_distance_index = k;
						gap_ref_start = k_ref_end;
						gap_ref_end   = i_ref_start;
						gap_query_start = k_query_end;
						gap_query_end   = i_query_start;
						combined_k_in_left = 1;
						combined_index_left = k;
						combined_index_right = i;
					}
				}
				// then, left: i-th chain, right: the k-th chain in the anchor 2D plot
				else if(i_ref_end < k_ref_start && i_query_end < k_query_start){
					manhattan = k_ref_start - i_ref_end + k_query_start - i_query_end;
					if(manhattan < manhattan_min){
						manhattan_min = manhattan;
						min_distance_index = k;
						gap_ref_start = i_ref_end;
						gap_ref_end   = k_ref_start;
						gap_query_start = i_query_end;
						gap_query_end   = k_query_start;
						combined_k_in_left = 0;
						combined_index_left = i;
						combined_index_right = k;
					}
				}				
			}
		}
		// then check whether another chain exist between i-th chain and the min_distance_index-th chain 
		// this is for the interspered repeat
		if(min_distance_index == -1 || manhattan_min >= 5000){ //min_distance_index = -1: the i-th chain overlaps with all other chains
			continue;
		}
		else{				
			for(k = 0; k < num_chain; k++){
				if (k == i || k == min_distance_index){
					continue;
				}
				max_start = gap_query_start >= chain_pos[k].pos_query_start ?  gap_query_start : chain_pos[k].pos_query_start;
				min_end   = gap_query_end <= chain_pos[k].pos_query_end ? gap_query_end : chain_pos[k].pos_query_end;
				if (max_start <= min_end){
					connected = 0;
					break;
				}
				// then check reference
				max_start = gap_ref_start >= chain_pos[k].pos_ref_start ? gap_ref_start : chain_pos[k].pos_ref_start;
				min_end   = gap_ref_end <= chain_pos[k].pos_ref_end ? gap_ref_end : chain_pos[k].pos_ref_end;
				if (max_start <= min_end){
				//if (chain_pos[k].pos_ref_start >= chain_pos[i - 1].pos_ref_end && chain_pos[k].pos_ref_end <= chain_pos[i].pos_ref_start){
					connected = 0;
					break;
				}
				connected = 1;
			}				
		}
			if(connected == 1){
				rechain = 1;
				// the i-th chain is in right, min_distance_index-th chain in left
				if(combined_k_in_left == 1){
					p[chain_pos[i].anchor_index_start] = chain_pos[min_distance_index].anchor_index_end;
					next[chain_pos[min_distance_index].anchor_index_end] = chain_pos[i].anchor_index_start;
					// then add the score
					k = chain_pos[i].anchor_index_start;
					//f[k] = f[chain_pos[connected_index].anchor_index_end] + 1;
					//k = next[k];
					while(next[k] > -1 ){
						f[k] = f[p[k]] + 1;
						k = next[k];
					}
					f[k] = f[p[k]] + 1;
					flag_chains[min_distance_index] = 1;
					// update the i-th chain
					chain_pos[i].anchor_index_start = chain_pos[min_distance_index].anchor_index_start;
					chain_pos[i].pos_ref_start      = chain_pos[min_distance_index].pos_ref_start;
					chain_pos[i].pos_query_start    = chain_pos[min_distance_index].pos_query_start;
				}				
				else{
					// the i-th chain is in left, min_distance_index-th chain in right
					p[chain_pos[min_distance_index].anchor_index_start] = chain_pos[i].anchor_index_end;
					next[chain_pos[i].anchor_index_end] = chain_pos[min_distance_index].anchor_index_start;
					k = chain_pos[min_distance_index].anchor_index_start;
					while(next[k] > -1 ){
						f[k] = f[p[k]] + 1;
						k = next[k];
					}
					f[k] = f[p[k]] + 1;
					flag_chains[min_distance_index] = 1;
					chain_pos[i].anchor_index_end   = chain_pos[min_distance_index].anchor_index_end;
					chain_pos[i].pos_ref_end        = chain_pos[min_distance_index].pos_ref_end;
					chain_pos[i].pos_query_end      = chain_pos[min_distance_index].pos_query_end;
				}
			}
		}
		// then again check the number of chains that has been conneced, for checking exist the while loop
		for(i = 0; i < num_chain - 1; i++){ 
			if(flag_chains[i] == 1){
				num_connected2 += 1;
			}			
		}
		if(num_connected1 == num_connected2){
			free(flag_chains);
			
		}
	}	


// mymymy combine 45-degree chain from high to low score

int combine_chain(mm64_t_each_chain *chain_pos, int32_t num_chain, int32_t *f, int64_t *p, int64_t *next, int32_t *rechain, const int *qlens){
	// determine whether two chains should be connected
	int32_t connected, manhattan, manhattan_min, i, min_distance_index, k, num_connected1, num_connected2, combined_k_in_left;
	int32_t i_ref_start, i_ref_end, i_query_start, i_query_end, k_ref_start, k_ref_end, k_query_start, k_query_end;
	int32_t gap_ref_start, gap_ref_end, gap_query_start, gap_query_end, max_start, min_end, dr, dq, dd;
	int8_t *flag_chains = (int8_t *)malloc(num_chain * sizeof(int8_t)), covered_by_ref, covered_by_query; // the flag for each chain, -1: combined, 1
	int32_t combined_index_left, combined_index_right, overlap_ref_min, overlap_ref_max, overlap_ref, overlap_query_min, overlap_query_max, overlap_query;//, length_i, length_k;
	float bili_first_chain, bili_query, bili_ref;
	bili_first_chain= (float)(chain_pos[0].pos_query_end - chain_pos[0].pos_query_start + 15) / *qlens;
	for(i = 0; i < num_chain; i++){
		flag_chains[i] = 0; // 0: not combined, 1 means has been conbined, 2: the chain is growing to be longer
		if(chain_pos[i].anchor_diversity < chain_pos[0].anchor_diversity / 2.0){
			flag_chains[i] = 1;
			chain_pos[i].rechain = 1;
		}
	}
	if (bili_first_chain >= 0.96){ // means on sv exist with high probability
		for(i = 1; i < num_chain; i++){
			chain_pos[i].rechain = 1;
		}
		*rechain = 1;
	}
	else{
		for(k = num_chain - 1; k > 0; k--){
			k_ref_start      = chain_pos[k].pos_ref_start;
			k_ref_end        = chain_pos[k].pos_ref_end;
			k_query_start    = chain_pos[k].pos_query_start;
			k_query_end   	 = chain_pos[k].pos_query_end;
			covered_by_ref   = 0;
			covered_by_query = 0;
			for(i = 0; i < k; i++){
				if(flag_chains[i] == 1){
					continue;
				}
				if(chain_pos[i].plus != chain_pos[k].plus){
					continue;
				}
				i_ref_start   = chain_pos[i].pos_ref_start;
				i_ref_end     = chain_pos[i].pos_ref_end;
				i_query_start = chain_pos[i].pos_query_start;
				i_query_end   = chain_pos[i].pos_query_end;
				bili_query = 0.0f;
				bili_ref   = 0.0f;
				//------------ 1, if one shorter chain is totally covered by another longer chain in reference and query, remove it.
		        //                   this longer chain can be one chain, or two chains 
				if (k_ref_start >= i_ref_start && k_ref_end <= i_ref_end){
					covered_by_ref = 1;
				}
				if (k_query_start >= i_query_start && k_query_end <= i_query_end){
					covered_by_query = 1;
				}				
				if(covered_by_ref == 1 && covered_by_query == 1){
					flag_chains[k] = 1;
					chain_pos[k].rechain = 1;
					*rechain = 1;
					break;
				}
				//----------  2, if one shorter chain is 80% covered by one longer chain in both reference and query, remove it.
		        				// query overlap
				overlap_query_min = (i_query_start > k_query_start) ? i_query_start : k_query_start;
				overlap_query_max = (i_query_end   < k_query_end)   ? i_query_end   : k_query_end;
				overlap_query = overlap_query_max - overlap_query_min;
				if (overlap_query < 0) {
					overlap_query = 0;
					//continue;    
				}
				//  reference overlap
				overlap_ref_min = (i_ref_start > k_ref_start) ? i_ref_start : k_ref_start;
				overlap_ref_max = (i_ref_end   < k_ref_end)   ? i_ref_end   : k_ref_end;
				overlap_ref = overlap_ref_max - overlap_ref_min;
				if (overlap_ref < 0) {
					overlap_ref = 0;
					//continue;
				}
				bili_query = (float)overlap_query / (k_query_end - i_query_start);
				if(bili_query >= 0.7 && covered_by_ref == 1){
					flag_chains[k] = 1;
					chain_pos[k].rechain = 1;
					*rechain = 1;
					break;
				}
				bili_ref   = (float)overlap_ref / (k_ref_end - k_ref_start);
				if(bili_ref >= 0.7 && covered_by_query == 1){
					flag_chains[k] = 1;
					chain_pos[k].rechain = 1;
					*rechain = 1;
					break;
				}
				if(bili_query >= 0.7 && bili_ref >= 0.7){
					flag_chains[k] = 1;
					chain_pos[k].rechain = 1;
					*rechain = 1;
					break;
				}			
			}
		}
		while(1){
			num_connected1 = 0;
			num_connected2 = 0;
			// first check the number of chains that has been conneced, for checking exist the while loop
			for(i = 0; i < num_chain; i++){ 
				if(flag_chains[i] == 1){
					num_connected1 += 1;
				}			
			}		
			for(i = 0; i < num_chain - 1; i++){
				if(flag_chains[i] == 1){ // 1: has been combined
					continue;
				}
				min_distance_index = -1;
				connected = 0;
				manhattan_min = INT32_MAX;
				i_ref_start   = chain_pos[i].pos_ref_start;
				i_ref_end     = chain_pos[i].pos_ref_end;
				i_query_start = chain_pos[i].pos_query_start;
				i_query_end   = chain_pos[i].pos_query_end;
				//length_i = i_query_end - i_query_start + 1;
				// first find the no-overlapping chain has the min manhattan distance with i-th chain
				for(k = i + 1; k < num_chain; k++){
					//if(k == i || flag_chains[k] == 1){ // 1: has been combined
					if(flag_chains[k] == 1){
						continue;
					}
					if(chain_pos[i].plus != chain_pos[k].plus){
						continue;
					}
					k_ref_start   = chain_pos[k].pos_ref_start;
					k_ref_end     = chain_pos[k].pos_ref_end;
					k_query_start = chain_pos[k].pos_query_start;
					k_query_end   = chain_pos[k].pos_query_end;
					// first, left: the k-th chain, right: i-th chain in the anchor 2D plot 
					if (i_ref_start > k_ref_end && i_query_start > k_query_end){						
						manhattan = i_ref_start - k_ref_end + i_query_start - k_query_end;
						if(manhattan < manhattan_min){
							manhattan_min = manhattan;
							min_distance_index = k;
							gap_ref_start = k_ref_end;
							gap_ref_end   = i_ref_start;
							gap_query_start = k_query_end;
							gap_query_end   = i_query_start;
							combined_k_in_left = 1;
							dr = i_ref_start - k_ref_end;
							dq = i_query_start - k_query_end;
							dd = dr > dq? dr - dq : dq - dr;
						}
					}
					// then, left: i-th chain, right: the k-th chain in the anchor 2D plot
					else if(i_ref_end < k_ref_start && i_query_end < k_query_start){
						manhattan = k_ref_start - i_ref_end + k_query_start - i_query_end;
						if(manhattan < manhattan_min){
							manhattan_min = manhattan;
							min_distance_index = k;
							gap_ref_start = i_ref_end;
							gap_ref_end   = k_ref_start;
							gap_query_start = i_query_end;
							gap_query_end   = k_query_start;
							combined_k_in_left = 0;
							dr = k_ref_start - i_ref_end;
							dq = k_query_start - i_query_end;
							dd = dr > dq? dr - dq : dq - dr;
						}
					}				
				}
				// then check whether another chain exist between i-th chain and the min_distance_index-th chain 
				// this is for the interspered repeat
				if(min_distance_index == -1 || dd >= 1500 || manhattan_min >= 5000){ //min_distance_index = -1: the i-th chain overlaps with all other chains
					continue;
				}
				
				else{
					connected = 1;	
					if(dr > 30 || dq > 30 || dd > 30){									
						for(k = num_chain - 1; k >= 0; k--){
							if (k == i || k == min_distance_index || flag_chains[k] == 1){
								continue;
							}
							max_start = gap_query_start >= chain_pos[k].pos_query_start ?  gap_query_start : chain_pos[k].pos_query_start;
							min_end   = gap_query_end <= chain_pos[k].pos_query_end ? gap_query_end : chain_pos[k].pos_query_end;
							if (max_start <= min_end){
								connected = 0;
								break;
							}
							// then check reference
							max_start = gap_ref_start >= chain_pos[k].pos_ref_start ? gap_ref_start : chain_pos[k].pos_ref_start;
							min_end   = gap_ref_end <= chain_pos[k].pos_ref_end ? gap_ref_end : chain_pos[k].pos_ref_end;
							if (max_start <= min_end){
							//if (chain_pos[k].pos_ref_start >= chain_pos[i - 1].pos_ref_end && chain_pos[k].pos_ref_end <= chain_pos[i].pos_ref_start){
								connected = 0;
								break;
							}
						}
					}				
				}
				if(connected == 1){
					*rechain = 1;
					// the i-th chain is in right, min_distance_index-th chain in left
					if(combined_k_in_left == 1){
						// the min_distance_index-th anchor index end should also < the i-th anchor index start
						if(chain_pos[min_distance_index].anchor_index_end >= chain_pos[i].anchor_index_start){
							*rechain = 0;
							continue;
						}
						p[chain_pos[i].anchor_index_start] = chain_pos[min_distance_index].anchor_index_end;
						next[chain_pos[min_distance_index].anchor_index_end] = chain_pos[i].anchor_index_start;
						// then add the score
						k = chain_pos[i].anchor_index_start;
						//f[k] = f[chain_pos[connected_index].anchor_index_end] + 1;
						//k = next[k];
						while(next[k] > -1 ){
							f[k] = f[p[k]] + 1;
							k = next[k];
						}
						f[k] = f[p[k]] + 1;
						if (i < min_distance_index){
							flag_chains[min_distance_index] = 1;
							chain_pos[min_distance_index].rechain = 1;
							flag_chains[i] = 2;
							chain_pos[i].rechain = 2;
							// update the i-th chain
							chain_pos[i].anchor_index_start = chain_pos[min_distance_index].anchor_index_start;
							chain_pos[i].pos_ref_start      = chain_pos[min_distance_index].pos_ref_start;
							chain_pos[i].pos_query_start    = chain_pos[min_distance_index].pos_query_start;
						}
						else{
							flag_chains[i] = 1;
							chain_pos[i].rechain = 1;
							// update the i-th chain
							chain_pos[min_distance_index].anchor_index_end = chain_pos[i].anchor_index_end;
							chain_pos[min_distance_index].pos_ref_end      = chain_pos[i].pos_ref_end;
							chain_pos[min_distance_index].pos_query_end    = chain_pos[i].pos_query_end;
						}
						
					}				
					else{// the i-th chain is in left, min_distance_index-th chain in right
						// the i-th anchor index end should also < the min_distance_index-th anchor index start
						if(chain_pos[i].anchor_index_end >= chain_pos[min_distance_index].anchor_index_start){
							*rechain = 0;
							continue;
						}
						p[chain_pos[min_distance_index].anchor_index_start] = chain_pos[i].anchor_index_end;
						next[chain_pos[i].anchor_index_end] = chain_pos[min_distance_index].anchor_index_start;
						k = chain_pos[min_distance_index].anchor_index_start;
						while(next[k] > -1 ){
							f[k] = f[p[k]] + 1;
							k = next[k];
						}
						f[k] = f[p[k]] + 1;
						if (i < min_distance_index){
							flag_chains[min_distance_index] = 1;
							chain_pos[min_distance_index].rechain = 1;
							flag_chains[i] = 2;
							chain_pos[i].rechain = 2;
							//update the i-th chain
							
							chain_pos[i].anchor_index_end   = chain_pos[min_distance_index].anchor_index_end;
							chain_pos[i].pos_ref_end        = chain_pos[min_distance_index].pos_ref_end;
							chain_pos[i].pos_query_end      = chain_pos[min_distance_index].pos_query_end;
						}
						else{
							flag_chains[i] = 1;
							chain_pos[i].rechain = 1;
							//update the i-th chain
							chain_pos[min_distance_index].anchor_index_start  = chain_pos[i].anchor_index_start;
							chain_pos[min_distance_index].pos_ref_start       = chain_pos[i].pos_ref_start;
							chain_pos[min_distance_index].pos_query_start     = chain_pos[i].pos_query_start;
						}
					}
				}
			}
			// then again check the number of chains that has been conneced, for checking exist the while loop
			for(i = 0; i < num_chain; i++){ 
				if(flag_chains[i] == 1){
					num_connected2 += 1;
				}			
			}
			if(num_connected1 == num_connected2){
				//free(flag_chains);
				bili_first_chain= (float)(chain_pos[0].pos_query_end - chain_pos[0].pos_query_start + 15) / *qlens;
				if (bili_first_chain >= 0.96){ // means on sv exist with high probability
					for(i = 1; i < num_chain; i++){
						chain_pos[i].rechain = 1;
					}
					*rechain = 1;
				}
				break;
			}
		}		
	}	
	//============================================  second round for combining
	for(k = num_chain - 1; k > 0; k--){
		if(flag_chains[k] == 1){
			continue;
		}
		k_ref_start      = chain_pos[k].pos_ref_start;
		k_ref_end        = chain_pos[k].pos_ref_end;
		k_query_start    = chain_pos[k].pos_query_start;
		k_query_end   	 = chain_pos[k].pos_query_end;
		covered_by_ref   = 0;
		covered_by_query = 0;
		for(i = 0; i < k; i++){
			if(flag_chains[i] == 1){
				continue;
			}
			if(chain_pos[i].plus != chain_pos[k].plus){
				continue;
			}
			i_ref_start   = chain_pos[i].pos_ref_start;
			i_ref_end     = chain_pos[i].pos_ref_end;
			i_query_start = chain_pos[i].pos_query_start;
			i_query_end   = chain_pos[i].pos_query_end;
			bili_query = 0.0f;
			bili_ref   = 0.0f;
			//------------ 1, if one shorter chain is totally covered by another longer chain in reference and query, remove it.
			//                   this longer chain can be one chain, or two chains 
			if (k_ref_start >= i_ref_start && k_ref_end <= i_ref_end){
				covered_by_ref = 1;
			}
			if (k_query_start >= i_query_start && k_query_end <= i_query_end){
				covered_by_query = 1;
			}				
			if(covered_by_ref == 1 && covered_by_query == 1){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}
			//----------  2, if one shorter chain is 80% covered by one longer chain in both reference and query, remove it.
							// query overlap
			overlap_query_min = (i_query_start > k_query_start) ? i_query_start : k_query_start;
			overlap_query_max = (i_query_end   < k_query_end)   ? i_query_end   : k_query_end;
			overlap_query = overlap_query_max - overlap_query_min;
			if (overlap_query < 0) {
				overlap_query = 0;
				//continue;    
			}
			//  reference overlap
			overlap_ref_min = (i_ref_start > k_ref_start) ? i_ref_start : k_ref_start;
			overlap_ref_max = (i_ref_end   < k_ref_end)   ? i_ref_end   : k_ref_end;
			overlap_ref = overlap_ref_max - overlap_ref_min;
			if (overlap_ref < 0) {
				overlap_ref = 0;
				//continue;
			}
			bili_query = (float)overlap_query / (k_query_end - i_query_start);
			if(bili_query >= 0.7 && covered_by_ref == 1){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}
			bili_ref   = (float)overlap_ref / (k_ref_end - k_ref_start);
			if(bili_ref >= 0.7 && covered_by_query == 1){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}
			if(bili_query >= 0.7 && bili_ref >= 0.7){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}			
		}
	}
	while(1){
		num_connected1 = 0;
		num_connected2 = 0;
		// first check the number of chains that has been conneced, for checking exist the while loop
		for(i = 0; i < num_chain; i++){ 
			if(flag_chains[i] == 1){
				num_connected1 += 1;
			}			
		}
		if(num_connected1 == num_chain - 1){
			break;
		}		
		for(i = 0; i < num_chain - 1; i++){
			if(flag_chains[i] == 1){ // 1: has been combined
				continue;
			}
			min_distance_index = -1;
			connected = 0;
			manhattan_min = INT32_MAX;
			i_ref_start   = chain_pos[i].pos_ref_start;
			i_ref_end     = chain_pos[i].pos_ref_end;
			i_query_start = chain_pos[i].pos_query_start;
			i_query_end   = chain_pos[i].pos_query_end;
			//length_i = i_query_end - i_query_start + 1;
			// first find the no-overlapping chain has the min manhattan distance with i-th chain
			for(k = i + 1; k < num_chain; k++){
				//if(k == i || flag_chains[k] == 1){ // 1: has been combined
				if(flag_chains[k] == 1){
					continue;
				}
				if(chain_pos[i].plus != chain_pos[k].plus){
					continue;
				}
				k_ref_start   = chain_pos[k].pos_ref_start;
				k_ref_end     = chain_pos[k].pos_ref_end;
				k_query_start = chain_pos[k].pos_query_start;
				k_query_end   = chain_pos[k].pos_query_end;
				// first, left: the k-th chain, right: i-th chain in the anchor 2D plot 
				if (i_ref_start > k_ref_end && i_query_start > k_query_end){						
					manhattan = i_ref_start - k_ref_end + i_query_start - k_query_end;
					if(manhattan < manhattan_min){
						manhattan_min = manhattan;
						min_distance_index = k;
						gap_ref_start = k_ref_end;
						gap_ref_end   = i_ref_start;
						gap_query_start = k_query_end;
						gap_query_end   = i_query_start;
						combined_k_in_left = 1;
						dr = i_ref_start - k_ref_end;
						dq = i_query_start - k_query_end;
						dd = dr > dq? dr - dq : dq - dr;
					}
				}
				// then, left: i-th chain, right: the k-th chain in the anchor 2D plot
				else if(i_ref_end < k_ref_start && i_query_end < k_query_start){
					manhattan = k_ref_start - i_ref_end + k_query_start - i_query_end;
					if(manhattan < manhattan_min){
						manhattan_min = manhattan;
						min_distance_index = k;
						gap_ref_start = i_ref_end;
						gap_ref_end   = k_ref_start;
						gap_query_start = i_query_end;
						gap_query_end   = k_query_start;
						combined_k_in_left = 0;
						dr = k_ref_start - i_ref_end;
						dq = k_query_start - i_query_end;
						dd = dr > dq? dr - dq : dq - dr;
					}
				}				
			}
			// then check whether another chain exist between i-th chain and the min_distance_index-th chain 
			// this is for the interspered repeat
			if(min_distance_index == -1 || dd >= 1000 || manhattan_min >= 5000){ //min_distance_index = -1: the i-th chain overlaps with all other chains
				continue;
			}
			else{
				connected = 1;	
				if(dd > 30){									
					for(k = num_chain - 1; k >= 0; k--){
						if (k == i || k == min_distance_index || flag_chains[k] == 1){
							continue;
						}
						max_start = gap_query_start >= chain_pos[k].pos_query_start ?  gap_query_start : chain_pos[k].pos_query_start;
						min_end   = gap_query_end <= chain_pos[k].pos_query_end ? gap_query_end : chain_pos[k].pos_query_end;
						if (max_start <= min_end){
							connected = 0;
							break;
						}
						// then check reference
						max_start = gap_ref_start >= chain_pos[k].pos_ref_start ? gap_ref_start : chain_pos[k].pos_ref_start;
						min_end   = gap_ref_end <= chain_pos[k].pos_ref_end ? gap_ref_end : chain_pos[k].pos_ref_end;
						if (max_start <= min_end){
						//if (chain_pos[k].pos_ref_start >= chain_pos[i - 1].pos_ref_end && chain_pos[k].pos_ref_end <= chain_pos[i].pos_ref_start){
							connected = 0;
							break;
						}
					}
				}				
			}
			if(connected == 1){
				*rechain = 1;
				// the i-th chain is in right, min_distance_index-th chain in left
				if(combined_k_in_left == 1){
					// the min_distance_index-th anchor index end should also < the i-th anchor index start
					if(chain_pos[min_distance_index].anchor_index_end >= chain_pos[i].anchor_index_start){
						*rechain = 0;
						continue;
					}
					p[chain_pos[i].anchor_index_start] = chain_pos[min_distance_index].anchor_index_end;
					next[chain_pos[min_distance_index].anchor_index_end] = chain_pos[i].anchor_index_start;
					// then add the score
					k = chain_pos[i].anchor_index_start;
					//f[k] = f[chain_pos[connected_index].anchor_index_end] + 1;
					//k = next[k];
					while(next[k] > -1 ){
						f[k] = f[p[k]] + 1;
						k = next[k];
					}
					f[k] = f[p[k]] + 1;
					if (i < min_distance_index){
						flag_chains[min_distance_index] = 1;
						chain_pos[min_distance_index].rechain = 1;
						flag_chains[i] = 2;
						chain_pos[i].rechain = 2;
						// update the i-th chain
						chain_pos[i].anchor_index_start = chain_pos[min_distance_index].anchor_index_start;
						chain_pos[i].pos_ref_start      = chain_pos[min_distance_index].pos_ref_start;
						chain_pos[i].pos_query_start    = chain_pos[min_distance_index].pos_query_start;
					}
					else{
						flag_chains[i] = 1;
						chain_pos[i].rechain = 1;
						// update the i-th chain
						chain_pos[min_distance_index].anchor_index_end = chain_pos[i].anchor_index_end;
						chain_pos[min_distance_index].pos_ref_end      = chain_pos[i].pos_ref_end;
						chain_pos[min_distance_index].pos_query_end    = chain_pos[i].pos_query_end;
					}
					
				}				
				else{// the i-th chain is in left, min_distance_index-th chain in right
					// the i-th anchor index end should also < the min_distance_index-th anchor index start
					if(chain_pos[i].anchor_index_end >= chain_pos[min_distance_index].anchor_index_start){
						*rechain = 0;
						continue;
					}
					p[chain_pos[min_distance_index].anchor_index_start] = chain_pos[i].anchor_index_end;
					next[chain_pos[i].anchor_index_end] = chain_pos[min_distance_index].anchor_index_start;
					k = chain_pos[min_distance_index].anchor_index_start;
					while(next[k] > -1 ){
						f[k] = f[p[k]] + 1;
						k = next[k];
					}
					f[k] = f[p[k]] + 1;
					if (i < min_distance_index){
						flag_chains[min_distance_index] = 1;
						chain_pos[min_distance_index].rechain = 1;
						flag_chains[i] = 2;
						chain_pos[i].rechain = 2;
						//update the i-th chain
						
						chain_pos[i].anchor_index_end   = chain_pos[min_distance_index].anchor_index_end;
						chain_pos[i].pos_ref_end        = chain_pos[min_distance_index].pos_ref_end;
						chain_pos[i].pos_query_end      = chain_pos[min_distance_index].pos_query_end;
					}
					else{
						flag_chains[i] = 1;
						chain_pos[i].rechain = 1;
						//update the i-th chain
						chain_pos[min_distance_index].anchor_index_start  = chain_pos[i].anchor_index_start;
						chain_pos[min_distance_index].pos_ref_start       = chain_pos[i].pos_ref_start;
						chain_pos[min_distance_index].pos_query_start     = chain_pos[i].pos_query_start;
					}
				}
			}
		}
		// then again check the number of chains that has been conneced, for checking exist the while loop
		for(i = 0; i < num_chain; i++){ 
			if(flag_chains[i] == 1){
				num_connected2 += 1;
			}			
		}
		if(num_connected1 == num_connected2){
			//free(flag_chains);
			bili_first_chain= (float)(chain_pos[0].pos_query_end - chain_pos[0].pos_query_start + 15) / *qlens;
			if (bili_first_chain >= 0.96){ // means on sv exist with high probability
				for(i = 1; i < num_chain; i++){
					chain_pos[i].rechain = 1;
				}
				*rechain = 1;
			}
			break;
		}
	}
	//================================ finally, check one chain is covered by longer chain
	for(k = num_chain - 1; k > 0; k--){
		if(flag_chains[k] == 1){
			continue;
		}
		k_ref_start      = chain_pos[k].pos_ref_start;
		k_ref_end        = chain_pos[k].pos_ref_end;
		k_query_start    = chain_pos[k].pos_query_start;
		k_query_end   	 = chain_pos[k].pos_query_end;
		covered_by_ref   = 0;
		covered_by_query = 0;
		for(i = 0; i < k; i++){
			if(flag_chains[i] == 1){
				continue;
			}
			if(chain_pos[i].plus != chain_pos[k].plus){
				continue;
			}
			i_ref_start   = chain_pos[i].pos_ref_start;
			i_ref_end     = chain_pos[i].pos_ref_end;
			i_query_start = chain_pos[i].pos_query_start;
			i_query_end   = chain_pos[i].pos_query_end;
			bili_query = 0.0f;
			bili_ref   = 0.0f;
			//------------ 1, if one shorter chain is totally covered by another longer chain in reference and query, remove it.
			//                   this longer chain can be one chain, or two chains 
			if (k_ref_start >= i_ref_start && k_ref_end <= i_ref_end){
				covered_by_ref = 1;
			}
			if (k_query_start >= i_query_start && k_query_end <= i_query_end){
				covered_by_query = 1;
			}				
			if(covered_by_ref == 1 && covered_by_query == 1){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}
			//----------  2, if one shorter chain is 80% covered by one longer chain in both reference and query, remove it.
							// query overlap
			overlap_query_min = (i_query_start > k_query_start) ? i_query_start : k_query_start;
			overlap_query_max = (i_query_end   < k_query_end)   ? i_query_end   : k_query_end;
			overlap_query = overlap_query_max - overlap_query_min;
			if (overlap_query < 0) {
				overlap_query = 0;
				//continue;    
			}
			//  reference overlap
			overlap_ref_min = (i_ref_start > k_ref_start) ? i_ref_start : k_ref_start;
			overlap_ref_max = (i_ref_end   < k_ref_end)   ? i_ref_end   : k_ref_end;
			overlap_ref = overlap_ref_max - overlap_ref_min;
			if (overlap_ref < 0) {
				overlap_ref = 0;
				//continue;
			}
			bili_query = (float)overlap_query / (k_query_end - i_query_start);
			if(bili_query >= 0.7 && covered_by_ref == 1){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}
			bili_ref   = (float)overlap_ref / (k_ref_end - k_ref_start);
			if(bili_ref >= 0.7 && covered_by_query == 1){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}
			if(bili_query >= 0.7 && bili_ref >= 0.7){
				flag_chains[k] = 1;
				chain_pos[k].rechain = 1;
				*rechain = 1;
				break;
			}			
		}
	}
	free(flag_chains);
}
//mymy
// if two chains are seperated by insert or delete, they should combine
uint64_t *mg_chain_backtrack_chains_combine(void *km, int64_t n, int32_t *f, int64_t *p, int32_t *v, int32_t *t, int32_t min_cnt, int32_t min_sc, int32_t max_drop, int32_t *n_u_, int32_t *n_v_, mm128_t *a, const int *qlens)
{
	mm128_t *z;
	uint64_t *u;
	int64_t i, k, n_z, n_v, connected_index, j;
	int32_t n_u, n_u1;
	//mymymy
	int64_t *next; // p[i] is the previous anchor for i-th anchor, next[i] is its next anchor
	next = Kmalloc(km, int64_t, n);
	for(i = 0; i < n; i++){ // first initialize to -1
		next[i] = -1;
	}
	*n_u_ = *n_v_ = 0;
	for (i = 0, n_z = 0; i < n; ++i) {// precompute n_z
		if (f[i] >= min_sc) {
			++n_z;
		}
	}
	if (n_z == 0) {
		return 0;
	}
	z = Kmalloc(km, mm128_t, n_z);
	for (i = 0, k = 0; i < n; ++i) {// populate z[]
		if (f[i] >= min_sc) {
			z[k].x = f[i], z[k++].y = i;//z[k].x: the anchor's score, z[k].y: the anchor's index
		}
	}
	radix_sort_128x(z, z + n_z);

	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // precompute n_u
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				++n_v, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				++n_u;
			else n_v = n_v0;
		}
	}
	if(n_u == 0){
		kfree(km, z);
		kfree(km, next);
		return 0;
	}
	n_u1 = n_u;
	u = Kmalloc(km, uint64_t, n_u);
	mm64_t_each_chain *chain_pos;
	int32_t chain_pos_min_ref = INT32_MAX, chain_pos_min_query  = INT32_MAX; // record the min position in query and reference
	chain_pos = Kmalloc(km, mm64_t_each_chain, n_u);
	memset(t, 0, n * 4);
	//mymymy
	//fprintf(stdout, "chain_id\tpos_ref\tpos_query\tstrand\n");
	//fprintf(stdout, "pos_ref\tpos_query\tchain_id\tstrand\n");
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // populate u[]
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			chain_pos[n_u].pos_ref_end = (int32_t)a[z[k].y].x;
			chain_pos[n_u].pos_query_end = (int32_t)a[z[k].y].y;
			chain_pos[n_u].anchor_index_end = z[k].y;
			chain_pos[n_u].rechain = 0;
			chain_pos[n_u].anchor_num = 0;
			chain_pos[n_u].anchor_diversity = 0.0f;
			chain_pos[n_u].plus = a[z[k].y].x >> 63 == 0 ? 1 : 0;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i]){
				v[n_v++] = i, t[i] = 1;
				chain_pos[n_u].anchor_index_start = i;
				chain_pos[n_u].pos_ref_start = (int32_t)a[i].x;
				chain_pos[n_u].pos_query_start = (int32_t)a[i].y;
				chain_pos[n_u].anchor_num += 1;
				if ((int32_t)a[i].x < chain_pos_min_ref) {
					chain_pos_min_ref = (int32_t)a[i].x;
				}
				if ((int32_t)a[i].y < chain_pos_min_query){
					chain_pos_min_query = (int32_t)a[i].y;
				}
			}
			chain_pos[n_u].anchor_diversity = (float)chain_pos[n_u].anchor_num / (chain_pos[n_u].pos_ref_end - chain_pos[n_u].pos_ref_start + 15);
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt){
				// then populate next array
				for(j = chain_pos[n_u].anchor_index_end; j >= chain_pos[n_u].anchor_index_start;){
					if(p[j] > -1){
						//fprintf(stdout, "%d\t%d\t%d\t%c\n", n_u, (int32_t)a[j].x, (int32_t)a[j].y, "+-"[a[j].x>>63]);
						next[p[j]] = j;
						j = p[j];
						//fprintf(stdout, "%d\t%d\t%d\t%c\n", (int32_t)a[j].x, (int32_t)a[j].y, n_u, "+-"[a[j].x>>63]);						
					}
					else{
						break;
					}
					
				}
				u[n_u++] = (uint64_t)sc << 32 | (n_v - n_v0);
				if (n_u == n_u1){
					break;
				}
			}
			else n_v = n_v0;
		}
	}
	int32_t rechain = 0, n_uu = n_u;
	combine_chain(chain_pos, n_u, f, p, next, &rechain, qlens);
	
	if (rechain == 1){
		kfree(km, u);
		n_u = 0;
		
		*n_u_ = *n_v_ = 0;
		// following /// means the original codes
		///for (i = 0, n_z = 0; i < n; ++i) {// precompute n_z
		///	if (f[i] >= min_sc) {
		///		++n_z;
		///	}
		///}
		for(i = 0, n_z = 0; i < n_uu; ++i){// precompute n_z
			if(chain_pos[i].rechain == 2 || chain_pos[i].rechain == 0){
				//n_z += chain_pos[i].anchor_num;
				n_u += 1;
			}
		}
		if (n_u == 0) {
			return 0;
		}
		u = Kmalloc(km, uint64_t, n_u);
		for(i = 0, n_v = n_u = 0; i < n_uu; ++i){
			if(chain_pos[i].rechain == 2 || chain_pos[i].rechain == 0){
				int64_t n_v0 = n_v;
				int32_t sc;
				for (k = chain_pos[i].anchor_index_end; k >= chain_pos[i].anchor_index_start; k = p[k]){
					v[n_v++] = k;
				}
				sc = f[chain_pos[i].anchor_index_end] - f[chain_pos[i].anchor_index_start];
				u[n_u++] = (uint64_t)sc << 32 | (n_v - n_v0);
			}
		}
		//if(n_u >= n_u1){
		//	int hahaha = 0;
		//}
		assert(n_u <= n_u1);
	} 
	kfree(km, z);
	kfree(km, chain_pos);
	kfree(km, next);
	assert(n_v < INT32_MAX);
	*n_u_ = n_u, *n_v_ = n_v;
	return u;
}


//mymymy  return all anchors located in the top-1 mapped region
uint64_t *mg_chain_backtrack_anchors_index(void *km, int64_t n, const int32_t *f, const int64_t *p, int32_t *v, int32_t *t, int32_t *anchor_keep, int32_t min_cnt, int32_t min_sc, int32_t max_drop, int32_t *n_u_, int32_t *n_v_, mm128_t *a, const int *qlens)
{
	//mm128_t *z;
	uint64_t *u;
	int64_t i, k, n_z, n_v, index_max_score, end_i, end_i_my;
	int32_t n_u, max_score = min_sc - 1;//, boundary_left, boundary_right;

	*n_u_ = *n_v_ = 0;
	for (i = 0, n_z = 0; i < n; ++i){ // precompute n_z
		if (f[i] >= min_sc) {
			++n_z;
			if (f[i] > max_score){
				max_score = f[i];
				index_max_score = i;
			}
		}
	}
	if (n_z == 0) {
		return 0;
	}	
	end_i_my = index_max_score;
	while (p[end_i_my] > -1){
		end_i_my = p[end_i_my];
	}
	/*
	/////////////////////////////////////////////////////////////////////////////////////////////////
	boundary_left  = (int32_t)a[end_i_my].x >= (int32_t)a[end_i_my].y * 1.2 ? (int32_t)a[end_i_my].x - (int32_t)a[end_i_my].y * 1.1: 0;
	boundary_right = (int32_t)a[index_max_score].x + (*qlens - (int32_t)a[index_max_score].y) * 1.1;
	//end_i = p[end_i];

	// keep the anchors in the region that > min_score
	n_z = 0;
	for (i = 0; i < n; i++){
		if((int32_t)a[i].x >= boundary_left && (int32_t)a[i].x <= boundary_right){
			if (f[i] >= min_sc){
				++n_z;
			}
		}
	}
	//for(i = end_i_my; i <= index_max_score; ++i){
	//	if (f[i] >= min_sc){
	//		++n_z;
	//	}
	//}
	if (n_z == 0){
		return 0;
	}
	z = Kmalloc(km, mm128_t, n_z);
	k = 0;
	for (i = 0; i < n; i++){
		if((int32_t)a[i].x >= boundary_left && (int32_t)a[i].x <= boundary_right){
			if (f[i] >= min_sc){
				z[k].x = f[i];
				z[k++].y = i;
			}
		}
	}
	//for(i = end_i_my; i <= index_max_score; ++i){
	//	if (f[i] >= min_sc) {
	//		z[k].x = f[i];
	//		z[k++].y = i;
	//	}
	//}
	radix_sort_128x(z, z + n_z);
	memset(t, 0, n * 4);
	fprintf(stdout, "pos_ref\tpos_query\tchain_id\tstrand\n");
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // precompute n_u
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i]){
				++n_v;
				t[i] = 1;
			}
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt){
				++n_u;
				for(i = z[k].y; i != end_i; i = p[i]){
					anchor_keep[i] = 1;
					fprintf(stdout, "%d\t%d\t%d\t%c\n", (int32_t)a[i].x, (int32_t)a[i].y, n_u, "+-"[a[i].x>>63]);
				}
			}
			else {
				n_v = n_v0;
			}
		}
	}
	kfree(km, z);
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	*/
	n_u = 2;
	u = Kmalloc(km, uint64_t, n_u);
	u[0] = end_i_my;
	u[1] = index_max_score;
	*n_u_ = n_u;
	return u;
}




//mymymy use provided anchors for backtracking
uint64_t *mg_chain_backtrack_dup(void *km, int64_t n, const int32_t *f, const int64_t *p, int32_t *v, int32_t *t, int32_t min_cnt, int32_t min_sc, int32_t max_drop, int32_t *n_u_, int32_t *n_v_, int32_t* index_for_bk, int32_t index_for_bk_num)
{
	//mm128_t *z;
	uint64_t *u;
	int64_t i, k, n_z, n_v;
	int32_t n_u;
	//mymymy
	/*
	*n_u_ = *n_v_ = 0;
	for (i = 0, n_z = 0; i < n; ++i) // precompute n_z
		if (f[i] >= min_sc) ++n_z;
	if (n_z == 0) return 0;
	z = Kmalloc(km, mm128_t, n_z);
	for (i = 0, k = 0; i < n; ++i) // populate z[]
		if (f[i] >= min_sc) z[k].x = f[i], z[k++].y = i;
	radix_sort_128x(z, z + n_z);

	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // precompute n_u
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				++n_v, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				++n_u;
			else n_v = n_v0;
		}
	}
	*/
	// mymymy 
	n_u = index_for_bk_num;
	u = Kmalloc(km, uint64_t, n_u);
	memset(t, 0, n * 4);
	for(k = 0, n_v = n_u = 0; k < index_for_bk_num; k++){ // populate u[] based on anchors_for_bk
		int64_t n_v0 = n_v, end_i;
		int32_t sc;
		i = index_for_bk[k];
		do{
			t[i] = 1;
			i = p[i];
			end_i = i;
		}while(i > -1 && t[i] == 0);
		for(i = index_for_bk[k]; i != end_i; i = p[i]){
			v[n_v++] = i;
			t[i] = 1;
		}
		sc = i < 0? f[index_for_bk[k]] : f[index_for_bk[k]] - f[i];
		u[n_u++] = (uint64_t)sc << 32 | (n_v - n_v0);
	}
	/*




	u = Kmalloc(km, uint64_t, n_u);
	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // populate u[]
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				v[n_v++] = i, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				u[n_u++] = (uint64_t)sc << 32 | (n_v - n_v0);
			else n_v = n_v0;
		}
	}
	kfree(km, z);
	*/
	assert(n_v < INT32_MAX);
	*n_u_ = n_u, *n_v_ = n_v;
	return u;
}


static mm128_t *compact_a(void *km, int32_t n_u, uint64_t *u, int32_t n_v, int32_t *v, mm128_t *a)
{
	mm128_t *b, *w;
	uint64_t *u2;
	int64_t i, j, k;

	// write the result to b[]
	b = Kmalloc(km, mm128_t, n_v);
	for (i = 0, k = 0; i < n_u; ++i) {
		int32_t k0 = k, ni = (int32_t)u[i];
		for (j = 0; j < ni; ++j)
			b[k++] = a[v[k0 + (ni - j - 1)]];
	}
	kfree(km, v);

	// sort u[] and a[] by the target position, such that adjacent chains may be joined
	w = Kmalloc(km, mm128_t, n_u);
	for (i = k = 0; i < n_u; ++i) {
		w[i].x = b[k].x, w[i].y = (uint64_t)k<<32|i;
		k += (int32_t)u[i];
	}
	radix_sort_128x(w, w + n_u);
	u2 = Kmalloc(km, uint64_t, n_u);
	for (i = k = 0; i < n_u; ++i) {
		int32_t j = (int32_t)w[i].y, n = (int32_t)u[j];
		u2[i] = u[j];
		memcpy(&a[k], &b[w[i].y>>32], n * sizeof(mm128_t));
		k += n;
	}
	memcpy(u, u2, n_u * 8);
	memcpy(b, a, k * sizeof(mm128_t)); // write _a_ to _b_ and deallocate _a_ because _a_ is oversized, sometimes a lot
	kfree(km, a); kfree(km, w); kfree(km, u2);
	return b;
}
//mymymy return all anchors in the top-1 mapped region 
static mm128_t *compact_a_all_anchors(void *km, int32_t n_u, uint64_t *u, int64_t n_a, int64_t *n_a2, int32_t *v, mm128_t *a, const int *qlens,  int32_t *anchor_keep)
{
	mm128_t *b;
	int64_t j, k;
	int32_t boundary_left, boundary_right, anchors_num = 0;
	boundary_left  = (int32_t)a[u[0]].x >= (int32_t)a[u[0]].y * 1.2 ? (int32_t)a[u[0]].x - (int32_t)a[u[0]].y * 1.2: 0;
	boundary_right = (int32_t)a[u[1]].x + (*qlens - (int32_t)a[u[1]].y) * 1.2;
	//precalculate anchors_num
	for (j = 0; j < n_a; j++){
		if((int32_t)a[j].x >= boundary_left && (int32_t)a[j].x <= boundary_right){
			anchors_num++;
		}
	}
	// write the result to b[]
	b = Kmalloc(km, mm128_t, anchors_num);
	for (j = 0, k = 0; j < n_a; j++) {
		if((int32_t)a[j].x >= boundary_left && (int32_t)a[j].x <= boundary_right){
			b[k++] = a[j];
		}
	}
	kfree(km, v);
	kfree(km, a);
	kfree(km, u);
	//kfree(km, anchor_keep);
	*n_a2 = anchors_num;
	return b;
}

static inline int32_t comput_sc(const mm128_t *ai, const mm128_t *aj, int32_t max_dist_x, int32_t max_dist_y, int32_t bw, float chn_pen_gap, float chn_pen_skip, int is_cdna, int n_seg)
{
	int32_t dq = (int32_t)ai->y - (int32_t)aj->y, dr, dd, dg, q_span, sc;
	int32_t sidi = (ai->y & MM_SEED_SEG_MASK) >> MM_SEED_SEG_SHIFT;
	int32_t sidj = (aj->y & MM_SEED_SEG_MASK) >> MM_SEED_SEG_SHIFT;
	if (dq <= 0 || dq > max_dist_x) return INT32_MIN;
	dr = (int32_t)(ai->x - aj->x);
	if (sidi == sidj && (dr == 0 || dq > max_dist_y)) return INT32_MIN;
	dd = dr > dq? dr - dq : dq - dr;
	float bili = dr >= dq? (float)dr / (float)dq : (float)dq / (float)dr;
	//if (dd >= 50 || bili > 2.0){
	//	return 20252025;
	//}
	if (sidi == sidj && dd > bw) return INT32_MIN;
	if (n_seg > 1 && !is_cdna && sidi == sidj && dr > max_dist_y) return INT32_MIN;
	dg = dr < dq? dr : dq;
	q_span = aj->y>>32&0xff;
	sc = q_span < dg? q_span : dg;
	if (dd || dg > q_span) {
		float lin_pen, log_pen;
		lin_pen = chn_pen_gap * (float)dd + chn_pen_skip * (float)dg;
		log_pen = dd >= 1? mg_log2(dd + 1) : 0.0f; // mg_log2() only works for dd>=2
		if (is_cdna || sidi != sidj) {
			if (sidi != sidj && dr == 0) ++sc; // possibly due to overlapping paired ends; give a minor bonus
			else if (dr > dq || sidi != sidj) sc -= (int)(lin_pen < log_pen? lin_pen : log_pen); // deletion or jump between paired ends
			else sc -= (int)(lin_pen + .5f * log_pen);
		} else sc -= (int)(lin_pen + .5f * log_pen);
	}
	return sc;
}
//mymymy scoring only 45 diagonal
static inline int32_t comput_sc_45_diagonal(const mm128_t *ai, const mm128_t *aj, int32_t max_dist_x, int32_t max_dist_y, int32_t bw, float chn_pen_gap, float chn_pen_skip, int is_cdna, int n_seg)
{
	int32_t dq = (int32_t)ai->y - (int32_t)aj->y, dr, dd, dg, q_span, sc, min_d;
	int32_t sidi = (ai->y & MM_SEED_SEG_MASK) >> MM_SEED_SEG_SHIFT;
	int32_t sidj = (aj->y & MM_SEED_SEG_MASK) >> MM_SEED_SEG_SHIFT;
	if (dq <= 0 || dq > max_dist_x) {
		return INT32_MIN;
	}
	dr = (int32_t)(ai->x - aj->x);
	if (sidi == sidj && (dr == 0 || dq > max_dist_y)) {
		return INT32_MIN;
	}
	dd = dr > dq? dr - dq : dq - dr;
	if (dd >= 30){
		return INT32_MIN;
	}
	//if (dr )
	float bili = dr >= dq? (float)dr / (float)dq : (float)dq / (float)dr;
	if (bili >= 1.09){
		return INT32_MIN;
	}

	//if(dr > 100 || dq > 100){
	//	return INT32_MIN;
	//}
	if (sidi == sidj && dd > bw) {
		return INT32_MIN;
	}
	if (n_seg > 1 && !is_cdna && sidi == sidj && dr > max_dist_y) {
		return INT32_MIN;
	}
	//return 1;
	dg = dr < dq? dr : dq;
	q_span = aj->y>>32&0xff;
	sc = q_span < dg? q_span : dg;
	if (dd || dg > q_span) {
		float lin_pen, log_pen;
		lin_pen = chn_pen_gap * (float)dd + chn_pen_skip * (float)dg;
		log_pen = dd >= 1? mg_log2(dd + 1) : 0.0f; // mg_log2() only works for dd>=2
		if (is_cdna || sidi != sidj) {
			if (sidi != sidj && dr == 0) ++sc; // possibly due to overlapping paired ends; give a minor bonus
			else if (dr > dq || sidi != sidj) sc -= (int)(lin_pen < log_pen? lin_pen : log_pen); // deletion or jump between paired ends
			else sc -= (int)(lin_pen + .5f * log_pen);
		} else sc -= (int)(lin_pen + .5f * log_pen);
	}
	return sc;
}
/* Input:
 *   a[].x: rev<<63 | tid<<32 | tpos
 *   a[].y: flags<<40 | q_span<<32 | q_pos
 * Output:
 *   n_u: #chains
 *   u[]: score<<32 | #anchors (sum of lower 32 bits of u[] is the returned length of a[])
 * input a[] is deallocated on return
 */
mm128_t *mg_lchain_dp_first_locate(int max_dist_x, int max_dist_y, int bw, int max_skip, int max_iter, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					  int is_cdna, int n_seg, int64_t *n, mm128_t *a, int *n_u_, uint64_t **_u, void *km, const int *qlens)
{ // TODO: make sure this works when n has more than 32 bits
	int32_t *f, *t, *v, n_u, n_v, mmax_f = 0, max_drop = bw, *anchor_keep;
	int64_t *p, i, j, max_ii, st = 0, nn_a = *n;
	uint64_t *u;

	if (_u) *_u = 0, *n_u_ = 0;
	if (*n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist_x < bw) max_dist_x = bw;
	if (max_dist_y < bw && !is_cdna) max_dist_y = bw;
	if (is_cdna) max_drop = INT32_MAX;
	p = Kmalloc(km, int64_t, *n);
	f = Kmalloc(km, int32_t, *n);
	v = Kmalloc(km, int32_t, *n);
	t = Kcalloc(km, int32_t, *n);
	//anchor_keep = Kcalloc(km, int32_t, *n); // 0: does not keep, 1: keep for 45-degree-chain

	// fill the score and backtrack arrays
	for (i = 0, max_ii = -1; i < *n; ++i) {
		//anchor_keep[i] = 0;
		int64_t max_j = -1, end_j;
		int32_t max_f = a[i].y>>32&0xff, score_start = max_f, n_skip = 0;
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist_x)) ++st;
		if (i - st > max_iter) st = i - max_iter;
		for (j = i - 1; j >= st; --j) {
			int32_t sc;
			sc = comput_sc(&a[i], &a[j], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			if (sc == INT32_MIN) continue;
			//if(sc == 20252025){ // 20252025 means it is a jump anchor
			//	sc = score_start - f[j];
			//}
			sc += f[j];
			if (sc > max_f) {
				max_f = sc, max_j = j;
				if (n_skip > 0) --n_skip;
			} else if (t[j] == (int32_t)i) {
				if (++n_skip > max_skip)
					break;
			}
			if (p[j] >= 0) t[p[j]] = i;
		}
		end_j = j;
		if (max_ii < 0 || a[i].x - a[max_ii].x > (int64_t)max_dist_x) {
			int32_t max = INT32_MIN;
			max_ii = -1;
			for (j = i - 1; j >= st; --j)
				if (max < f[j]) max = f[j], max_ii = j;
		}
		if (max_ii >= 0 && max_ii < end_j) {
			int32_t tmp;
			tmp = comput_sc(&a[i], &a[max_ii], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			//if(tmp == 20252025){ // 20252025 means it is a jump anchor
			//	tmp = score_start - f[max_ii];
			//}
			if (tmp != INT32_MIN && max_f < tmp + f[max_ii])
				max_f = tmp + f[max_ii], max_j = max_ii;
		}
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (max_ii < 0 || (a[i].x - a[max_ii].x <= (int64_t)max_dist_x && f[max_ii] < f[i]))
			max_ii = i;
		if (mmax_f < max_f) mmax_f = max_f;
		//fprintf(stderr, "X1\t%ld\t%ld:%d\t%ld\t%ld:%d\t%ld\t%ld\n", (long)i, (long)(a[i].x>>32), (int32_t)a[i].x, (long)max_j, max_j<0?-1L:(long)(a[max_j].x>>32), max_j<0?-1:(int32_t)a[max_j].x, (long)max_f, (long)v[i]);
	}

	u = mg_chain_backtrack_anchors_index(km, nn_a, f, p, v, t, anchor_keep, min_cnt, min_sc, max_drop, &n_u, &n_v, a, qlens);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	//int64_t n_a2 = 0;	
	return compact_a_all_anchors(km, n_u, u, nn_a, n, v, a, qlens, anchor_keep);
	//*n = n_a2;
}

mm128_t *mg_lchain_dp(int max_dist_x, int max_dist_y, int bw, int max_skip, int max_iter, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					  int is_cdna, int n_seg, int64_t n, mm128_t *a, int *n_u_, uint64_t **_u, void *km)
{ // TODO: make sure this works when n has more than 32 bits
	int32_t *f, *t, *v, n_u, n_v, mmax_f = 0, max_drop = bw;
	int64_t *p, i, j, max_ii, st = 0;
	uint64_t *u;

	if (_u) *_u = 0, *n_u_ = 0;
	if (n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist_x < bw) max_dist_x = bw;
	if (max_dist_y < bw && !is_cdna) max_dist_y = bw;
	if (is_cdna) max_drop = INT32_MAX;
	p = Kmalloc(km, int64_t, n);
	f = Kmalloc(km, int32_t, n);
	v = Kmalloc(km, int32_t, n);
	t = Kcalloc(km, int32_t, n);

	// fill the score and backtrack arrays
	for (i = 0, max_ii = -1; i < n; ++i) {
		int64_t max_j = -1, end_j;
		int32_t max_f = a[i].y>>32&0xff, score_start = max_f, n_skip = 0;
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist_x)) ++st;
		if (i - st > max_iter) st = i - max_iter;
		for (j = i - 1; j >= st; --j) {
			int32_t sc;
			sc = comput_sc(&a[i], &a[j], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			if (sc == INT32_MIN) continue;
			//if(sc == 20252025){ // 20252025 means it is a jump anchor
			//	sc = score_start - f[j];
			//}
			sc += f[j];
			if (sc > max_f) {
				max_f = sc, max_j = j;
				if (n_skip > 0) --n_skip;
			} else if (t[j] == (int32_t)i) {
				if (++n_skip > max_skip)
					break;
			}
			if (p[j] >= 0) t[p[j]] = i;
		}
		end_j = j;
		if (max_ii < 0 || a[i].x - a[max_ii].x > (int64_t)max_dist_x) {
			int32_t max = INT32_MIN;
			max_ii = -1;
			for (j = i - 1; j >= st; --j)
				if (max < f[j]) max = f[j], max_ii = j;
		}
		if (max_ii >= 0 && max_ii < end_j) {
			int32_t tmp;
			tmp = comput_sc(&a[i], &a[max_ii], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			//if(tmp == 20252025){ // 20252025 means it is a jump anchor
			//	tmp = score_start - f[max_ii];
			//}
			if (tmp != INT32_MIN && max_f < tmp + f[max_ii])
				max_f = tmp + f[max_ii], max_j = max_ii;
		}
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (max_ii < 0 || (a[i].x - a[max_ii].x <= (int64_t)max_dist_x && f[max_ii] < f[i]))
			max_ii = i;
		if (mmax_f < max_f) mmax_f = max_f;
		//fprintf(stderr, "X1\t%ld\t%ld:%d\t%ld\t%ld:%d\t%ld\t%ld\n", (long)i, (long)(a[i].x>>32), (int32_t)a[i].x, (long)max_j, max_j<0?-1L:(long)(a[max_j].x>>32), max_j<0?-1:(int32_t)a[max_j].x, (long)max_f, (long)v[i]);
	}

	u = mg_chain_backtrack(km, n, f, p, v, t, min_cnt, min_sc, max_drop, &n_u, &n_v);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	return compact_a(km, n_u, u, n_v, v, a);
}


//mymymy  after chaining by minimap2, chain again only compute the 45du anchors
mm128_t *mg_lchain_dp_45_diagonal(int max_dist_x, int max_dist_y, int bw, int max_skip, int max_iter, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					  int is_cdna, int n_seg, int64_t n, mm128_t *a, int *n_u_, uint64_t **_u, void *km, const int *qlens)
{ // TODO: make sure this works when n has more than 32 bits
	int32_t *f, *t, *v, n_u, n_v, mmax_f = 0, max_drop = bw;// manhattan_dis = 0, manhattan_dis_max;
	int64_t *p, i, j, max_ii, st = 0, pre_scored_num; // if pre_scored_num >= 30, stop scoring for current anchor
	uint64_t *u;

	if (_u) *_u = 0, *n_u_ = 0;
	if (n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist_x < bw) max_dist_x = bw;
	if (max_dist_y < bw && !is_cdna) max_dist_y = bw;
	if (is_cdna) max_drop = INT32_MAX;
	p = Kmalloc(km, int64_t, n);
	f = Kmalloc(km, int32_t, n);
	v = Kmalloc(km, int32_t, n);
	t = Kcalloc(km, int32_t, n);
	//for (i = 0; i < n; ++i){
	//	f[i] = -1;
	//}

	// fill the score and backtrack arrays
	for (i = 0, max_ii = -1; i < n; ++i) {
		f[i] = -1;
		pre_scored_num = 0;
		//manhattan_dis_max = INT32_MIN;
		int64_t max_j = -1, end_j;
		int32_t max_f = a[i].y>>32&0xff, score_start = max_f, n_skip = 0;
		// add one condition: the farthest pre-anchor is along the 45-degree within 100 bp
		// original: 
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist_x)){
		//int32_t dq = (int32_t)a[i].y - (int32_t)a[st].y, dr = (int32_t)a[i].x - (int32_t)a[st].x;
		//while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist_x) && (dq >= 100 && dr >= 100)) {
			++st;
			//dq = (int32_t)a[i].y - (int32_t)a[st].y;
			//dr = (int32_t)a[i].x - (int32_t)a[st].x;
		}
		if (i - st > max_iter){
			st = i - max_iter;
		}
		for (j = i - 1; j >= st; --j) {
			int32_t sc;
			sc = comput_sc_45_diagonal(&a[i], &a[j], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			if (sc == INT32_MIN) {
				if(f[j] > 15){
					pre_scored_num++;
					if(pre_scored_num >= 100){ // to avoid connecting the far pre anchor
						break;
					}
				}
				continue;
			}
			//if(sc == 20252025){ // 20252025 means it is a jump anchor
			//	sc = score_start - f[j];
			//}
			sc += f[j];
			if (sc > max_f) {
				max_f = sc, max_j = j;
				if (n_skip > 0) --n_skip;
			} else if (t[j] == (int32_t)i) {
				if (++n_skip > max_skip)
					break;
			}
			if (p[j] >= 0) {
				t[p[j]] = i;
			}
		}
		end_j = j;
		////mymymy
		/*
		if (max_ii < 0 || a[i].x - a[max_ii].x > (int64_t)max_dist_x) {
			int32_t max = INT32_MIN;
			max_ii = -1;
			for (j = i - 1; j >= st; --j)
				if (max < f[j]) max = f[j], max_ii = j;
		}
		if (max_ii >= 0 && max_ii < end_j) {
			int32_t tmp;
			tmp = comput_sc(&a[i], &a[max_ii], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			//if(tmp == 20252025){ // 20252025 means it is a jump anchor
			//	tmp = score_start - f[max_ii];
			//}
			if (tmp != INT32_MIN && max_f < tmp + f[max_ii])
				max_f = tmp + f[max_ii], max_j = max_ii;
		}
		*/
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (max_ii < 0 || (a[i].x - a[max_ii].x <= (int64_t)max_dist_x && f[max_ii] < f[i])){
			max_ii = i;
		}
		if (mmax_f < max_f) {
			mmax_f = max_f;
		}
		//fprintf(stderr, "X1\t%ld\t%ld:%d\t%ld\t%ld:%d\t%ld\t%ld\n", (long)i, (long)(a[i].x>>32), (int32_t)a[i].x, (long)max_j, max_j<0?-1L:(long)(a[max_j].x>>32), max_j<0?-1:(int32_t)a[max_j].x, (long)max_f, (long)v[i]);
	}

	//u = mg_chain_backtrack(km, n, f, p, v, t, min_cnt, min_sc, max_drop, &n_u, &n_v);
	// if two chains are seperated by insert or delete, they should combine
	u = mg_chain_backtrack_chains_combine(km, n, f, p, v, t, min_cnt, min_sc, max_drop, &n_u, &n_v, a, qlens);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	return compact_a(km, n_u, u, n_v, v, a);
}


/* Input:
 *   a[].x: rev<<63 | tid<<32 | tpos
 *   a[].y: flags<<40 | q_span<<32 | q_pos
 * Output:
 *   n_u: #chains
 *   u[]: score<<32 | #anchors (sum of lower 32 bits of u[] is the returned length of a[])
 * input a[] is deallocated on return
 */
mm128_t *mg_lchain_dp_dup(int max_dist_x, int max_dist_y, int bw, int max_skip, int max_iter, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					  int is_cdna, int n_seg, int64_t n, mm128_t *a, int *n_u_, uint64_t **_u, void *km, mm128_t* anchors_for_bk, int32_t anchors_for_bk_num)
{ // TODO: make sure this works when n has more than 32 bits
	int32_t *f, *t, *v, *index_bk, n_u, n_v, mmax_f = 0, max_drop = bw, index_bk_num = 0, kk;
	int64_t *p, i, j, max_ii, st = 0;
	uint64_t *u;

	if (_u) *_u = 0, *n_u_ = 0;
	if (n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist_x < bw) max_dist_x = bw;
	if (max_dist_y < bw && !is_cdna) max_dist_y = bw;
	if (is_cdna) max_drop = INT32_MAX;
	p = Kmalloc(km, int64_t, n);
	f = Kmalloc(km, int32_t, n);
	v = Kmalloc(km, int32_t, n);
	t = Kcalloc(km, int32_t, n);
	//mymymy
	index_bk = Kmalloc(km, int32_t, anchors_for_bk_num);
	// fill the score and backtrack arrays
	for (i = 0, max_ii = -1; i < n; ++i) {		
		int64_t max_j = -1, end_j;
		int32_t max_f = a[i].y>>32&0xff, n_skip = 0;
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist_x)) ++st;
		if (i - st > max_iter) st = i - max_iter;
		for (j = i - 1; j >= st; --j) {
			int32_t sc;
			sc = comput_sc(&a[i], &a[j], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			if (sc == INT32_MIN) continue;
			sc += f[j];
			if (sc > max_f) {
				max_f = sc, max_j = j;
				if (n_skip > 0) --n_skip;
			} else if (t[j] == (int32_t)i) {
				if (++n_skip > max_skip)
					break;
			}
			if (p[j] >= 0) t[p[j]] = i;
		}
		end_j = j;
		if (max_ii < 0 || a[i].x - a[max_ii].x > (int64_t)max_dist_x) {
			int32_t max = INT32_MIN;
			max_ii = -1;
			for (j = i - 1; j >= st; --j)
				if (max < f[j]) max = f[j], max_ii = j;
		}
		if (max_ii >= 0 && max_ii < end_j) {
			int32_t tmp;
			tmp = comput_sc(&a[i], &a[max_ii], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			if (tmp != INT32_MIN && max_f < tmp + f[max_ii])
				max_f = tmp + f[max_ii], max_j = max_ii;
		}
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (max_ii < 0 || (a[i].x - a[max_ii].x <= (int64_t)max_dist_x && f[max_ii] < f[i]))
			max_ii = i;
		if (mmax_f < max_f) mmax_f = max_f;
		//fprintf(stderr, "X1\t%ld\t%ld:%d\t%ld\t%ld:%d\t%ld\t%ld\n", (long)i, (long)(a[i].x>>32), (int32_t)a[i].x, (long)max_j, max_j<0?-1L:(long)(a[max_j].x>>32), max_j<0?-1:(int32_t)a[max_j].x, (long)max_f, (long)v[i]);
	}
	//mymymy fine the anchor index for backtracking
	for (kk = 0; kk < anchors_for_bk_num; kk++){
		for(i = 0; i < n; ++i){
			if(a[i].x == anchors_for_bk[kk].x && a[i].y == anchors_for_bk[kk].y){
				index_bk[index_bk_num++] = i;
				break;
			}
		}
	}
	if(index_bk_num != anchors_for_bk_num){
		fprintf(stderr, " Can not find anchors for backtracking in the second chaining step! Exist!\n");
		return 0;
	}

	u = mg_chain_backtrack_dup(km, n, f, p, v, t, min_cnt, min_sc, max_drop, &n_u, &n_v, index_bk, index_bk_num);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	return compact_a(km, n_u, u, n_v, v, a);
}




typedef struct lc_elem_s {
	int32_t y;
	int64_t i;
	double pri;
	KRMQ_HEAD(struct lc_elem_s) head;
} lc_elem_t;

#define lc_elem_cmp(a, b) ((a)->y < (b)->y? -1 : (a)->y > (b)->y? 1 : ((a)->i > (b)->i) - ((a)->i < (b)->i))
#define lc_elem_lt2(a, b) ((a)->pri < (b)->pri)
KRMQ_INIT(lc_elem, lc_elem_t, head, lc_elem_cmp, lc_elem_lt2)

KALLOC_POOL_INIT(rmq, lc_elem_t)

static inline int32_t comput_sc_simple(const mm128_t *ai, const mm128_t *aj, float chn_pen_gap, float chn_pen_skip, int32_t *exact, int32_t *width)
{
	int32_t dq = (int32_t)ai->y - (int32_t)aj->y, dr, dd, dg, q_span, sc;
	dr = (int32_t)(ai->x - aj->x);
	*width = dd = dr > dq? dr - dq : dq - dr;
	dg = dr < dq? dr : dq;
	q_span = aj->y>>32&0xff;
	sc = q_span < dg? q_span : dg;
	if (exact) *exact = (dd == 0 && dg <= q_span);
	if (dd || dq > q_span) {
		float lin_pen, log_pen;
		lin_pen = chn_pen_gap * (float)dd + chn_pen_skip * (float)dg;
		log_pen = dd >= 1? mg_log2(dd + 1) : 0.0f; // mg_log2() only works for dd>=2
		sc -= (int)(lin_pen + .5f * log_pen);
	}
	return sc;
}

mm128_t *mg_lchain_rmq(int max_dist, int max_dist_inner, int bw, int max_chn_skip, int cap_rmq_size, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					   int64_t n, mm128_t *a, int *n_u_, uint64_t **_u, void *km)
{
	int32_t *f,*t, *v, n_u, n_v, mmax_f = 0, max_rmq_size = 0, max_drop = bw;
	int64_t *p, i, i0, st = 0, st_inner = 0;
	uint64_t *u;
	lc_elem_t *root = 0, *root_inner = 0;
	void *mem_mp = 0;
	kmp_rmq_t *mp;

	if (_u) *_u = 0, *n_u_ = 0;
	if (n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist < bw) max_dist = bw;
	if (max_dist_inner < 0) max_dist_inner = 0;
	if (max_dist_inner > max_dist) max_dist_inner = max_dist;
	p = Kmalloc(km, int64_t, n);
	f = Kmalloc(km, int32_t, n);
	t = Kcalloc(km, int32_t, n);
	v = Kmalloc(km, int32_t, n);
	mem_mp = km_init2(km, 0x10000);
	mp = kmp_init_rmq(mem_mp);

	// fill the score and backtrack arrays
	for (i = i0 = 0; i < n; ++i) {
		int64_t max_j = -1;
		int32_t q_span = a[i].y>>32&0xff, max_f = q_span;
		lc_elem_t s, *q, *r, lo, hi;
		// add in-range anchors
		if (i0 < i && a[i0].x != a[i].x) {
			int64_t j;
			for (j = i0; j < i; ++j) {
				q = kmp_alloc_rmq(mp);
				q->y = (int32_t)a[j].y, q->i = j, q->pri = -(f[j] + 0.5 * chn_pen_gap * ((int32_t)a[j].x + (int32_t)a[j].y));
				krmq_insert(lc_elem, &root, q, 0);
				if (max_dist_inner > 0) {
					r = kmp_alloc_rmq(mp);
					*r = *q;
					krmq_insert(lc_elem, &root_inner, r, 0);
				}
			}
			i0 = i;
		}
		// get rid of active chains out of range
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist || krmq_size(head, root) > cap_rmq_size)) {
			s.y = (int32_t)a[st].y, s.i = st;
			if ((q = krmq_find(lc_elem, root, &s, 0)) != 0) {
				q = krmq_erase(lc_elem, &root, q, 0);
				kmp_free_rmq(mp, q);
			}
			++st;
		}
		if (max_dist_inner > 0)  { // similar to the block above, but applied to the inner tree
			while (st_inner < i && (a[i].x>>32 != a[st_inner].x>>32 || a[i].x > a[st_inner].x + max_dist_inner || krmq_size(head, root_inner) > cap_rmq_size)) {
				s.y = (int32_t)a[st_inner].y, s.i = st_inner;
				if ((q = krmq_find(lc_elem, root_inner, &s, 0)) != 0) {
					q = krmq_erase(lc_elem, &root_inner, q, 0);
					kmp_free_rmq(mp, q);
				}
				++st_inner;
			}
		}
		// RMQ
		lo.i = INT32_MAX, lo.y = (int32_t)a[i].y - max_dist;
		hi.i = 0, hi.y = (int32_t)a[i].y;
		if ((q = krmq_rmq(lc_elem, root, &lo, &hi)) != 0) {
			int32_t sc, exact, width, n_skip = 0;
			int64_t j = q->i;
			assert(q->y >= lo.y && q->y <= hi.y);
			sc = f[j] + comput_sc_simple(&a[i], &a[j], chn_pen_gap, chn_pen_skip, &exact, &width);
			if (width <= bw && sc > max_f) max_f = sc, max_j = j;
			if (!exact && root_inner && (int32_t)a[i].y > 0) {
				lc_elem_t *lo, *hi;
				s.y = (int32_t)a[i].y - 1, s.i = n;
				krmq_interval(lc_elem, root_inner, &s, &lo, &hi);
				if (lo) {
					const lc_elem_t *q;
					int32_t width;
					krmq_itr_t(lc_elem) itr;
					krmq_itr_find(lc_elem, root_inner, lo, &itr);
					while ((q = krmq_at(&itr)) != 0) {
						if (q->y < (int32_t)a[i].y - max_dist_inner) break;
						j = q->i;
						sc = f[j] + comput_sc_simple(&a[i], &a[j], chn_pen_gap, chn_pen_skip, 0, &width);
						if (width <= bw) {
							if (sc > max_f) {
								max_f = sc, max_j = j;
								if (n_skip > 0) --n_skip;
							} else if (t[j] == (int32_t)i) {
								if (++n_skip > max_chn_skip)
									break;
							}
							if (p[j] >= 0) t[p[j]] = i;
						}
						if (!krmq_itr_prev(lc_elem, &itr)) break;
					}
				}
			}
		}
		// set max
		assert(max_j < 0 || (a[max_j].x < a[i].x && (int32_t)a[max_j].y < (int32_t)a[i].y));
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (mmax_f < max_f) mmax_f = max_f;
		if (max_rmq_size < krmq_size(head, root)) max_rmq_size = krmq_size(head, root);
	}
	km_destroy(mem_mp);

	u = mg_chain_backtrack(km, n, f, p, v, t, min_cnt, min_sc, max_drop, &n_u, &n_v);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	return compact_a(km, n_u, u, n_v, v, a);
}
