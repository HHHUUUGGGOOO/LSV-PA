#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_map>
#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/util/abc_global.h"
#include "map/mio/mio.h"
#include <assert.h>

using namespace std;

/*=== src/base/abci/abcDar.c ==========================================*/
extern "C"
{
    Aig_Man_t *  Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// add new command
static int LSV_CommandOrBidec(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_or_bidec", LSV_CommandOrBidec, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = { init, destroy };

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ** some useful function **
// abc.h --> Abc_ObjIsPi(pObj), Abc_ObjIsPo(pObj)
// abc.h --> Abc_ObjForEachFanin(), Abc_ObjForEachFanout()
// abc.h --> Abc_NtkForEachPi(), Abc_NtkForEachPo()

/----------------------------------------------------------------------
//    Type define
//----------------------------------------------------------------------
// Types to hold vector-of-ints (Vi) and vector-of-vector-of-ints (Vvi)
typedef std::vector<int> Vi;
typedef std::vector<Vi> Vvi;

//----------------------------------------------------------------------
//    function definition
//---------------------------------------------------------------------- 
void cart_product_sop(
  Vvi& rvvi, // final result
  Vi& rvi, // current result
  Vvi::const_iterator me, // current input
  Vvi::const_iterator end) // final input
{
  if (me == end) 
  {
    // terminal condition of the recursion. We no longer have
    // any input vectors to manipulate. Add the current result (rvi)
    // to the total set of results (rvvi).
    rvvi.push_back(rvi);
    return;
  }
  
  // need an easy name for my vector-of-ints
  const Vi& mevi = *me;
  for (Vi::const_iterator it = mevi.begin() ; it != mevi.end() ; it++)
  {
    // final rvi will look like "a, b, c, ME, d, e, f"
    // At the moment, rvi already has "a, b, c"
    rvi.push_back(*it); // add ME
    cart_product_sop(rvvi, rvi, me+1, end); // add "d, e, f"
    rvi.pop_back(); // clean ME off for next round
  }
}

Vvi refine_cube_idx(Vvi& cube_idx)
{ 
  // refine (1) : 把每個 cube 重複的 element 刪掉 (https://reurl.cc/l95ZxE)
    // input : [[a, b, a], [a, b, d], [a, d, a], ..., [c, d, d]]
    // output : [[a, b], [a, b, d], [a, d], ..., [c, d]]
  for (int i = 0 ; i < cube_idx.size() ; ++i)
  {
    sort(cube_idx[i].begin(), cube_idx[i].end());
    cube_idx[i].erase(unique(cube_idx[i].begin(), cube_idx[i].end()), cube_idx[i].end());
  }
  // refine (2) : 把每個被包含的 cube 刪掉 (vector sort 完可用 "==" 比較)
    // input : [[a, b, d], [a, d], [a, c, d], [a, d], [a]]
    // output : [[a]]
    // 先 duplicate 一份 cube_idx, 如果有包含的話, 把被包含的那個從 duplicate 中刪掉 (erase ?)
  Vvi ans = cube_idx;
  for (int i = 0 ; i < cube_idx.size() ; ++i)
  {
    for (int j = 0 ; j < cube_idx.size() ; ++j)
    {
      if (cube_idx[i] == cube_idx[j]) { continue; }
      // 檢查是否包含
      else 
      {
        vector set_diff;
        vector::iterator it;
        it = set_difference(cube_idx[i].begin(), cube_idx[i].end(), cube_idx[j].begin(), cube_idx[j].end(), set_diff.begin());
        if (cube_idx[i].size() == cube_idx[j].size() + int(it - set_diff.begin()))
        {
          // cube_idx[i] 要被刪掉
          auto iter = std::remove(ans.begin(), ans.end(), cube_idx[i]);
          ans.erase(iter, ans.end());
          break;
        }
      }
    }
  }
  // return
  return ans;
}

vector<char*> one_cube_complement(vector<char*>& sop_list, int sop_length)
{
  string sop_0(sop_list[0]);
  vector<char*> temp_sop;
  for (int i = 0 ; i < sop_length ; ++i)
  {
    if (sop_0[i] == "1")
    {
      string temp_str(sop_length, '-');
      temp_str.replace(i, 1, "0");
      temp_sop.push_back(temp_str.c_str());
    }
    else if (sop_0[i] == "0")
    {
      string temp_str(sop_length, '-');
      temp_str.replace(i, 1, "1");
      temp_sop.push_back(temp_str.c_str());
    }
  }
  return temp_sop;
}

vector<char*> multi_cube_complement(vector<char*>& sop_list, int sop_length)
{
  // int = 0 --> offset ; int = 1 --> onset ; int = 2 --> don't care
  vector<int> onset_or_offset(sop_length, 2);
  vector<vector<int>> cube_idx;
  for (int i = 0 ; i < sop_list.size() ; ++i)
  {
    vector<int> temp_idx;
    for (int j = 0 ; j < sop_length ; ++j)
    {
      if (sop_list[i][j] == "0") { onset_or_offset[j] = 0; temp_idx.push_back(j); }
      else if (sop_list[i][j] == "1") { onset_or_offset[j] = 1; temp_idx.push_back(j); }
    }
    cube_idx.push_back(temp_idx);
  }
  // 同 program.cc 作法, 先不管每個 lit 的 phase, 做 cart_product
  Vvi output;
  Vi outputTemp;
  cart_product_sop(output, outputTemp, cube_idx.begin(), cube_idx.end());
  // refine "Vvi output"
  Vvi refined_sop;
  refined_sop = refine_cube_idx(output);
  // 將 output 轉成 char* pSop
  vector<char*> temp_sop;
  for (int i = 0 ; i < refined_sop.size() ; ++i)
  {
    string temp_ans(sop_length, '-');
    for (int j = 0 ; j < refined_sop[i].size() ; ++j)
    {
      // need to invert phase
      if (onset_or_offset[refined_sop[i][j]] == 0) { temp_ans.replace(refined_sop[i][j], 1, "1"); }
      else if (onset_or_offset[refined_sop[i][j]] == 1) { temp_ans.replace(refined_sop[i][j], 1, "0"); }
    }
    temp_sop.push_back(temp_ans);
  }
  return temp_sop;
}

void combine_fanin_sop(vector<char*>& combined_sop, vector<char*>& fanin0_sop, vector<char*>& fanin1_sop, int sop_length)
{
  // int = 0 --> offset ; int = 1 --> onset ; int = 2 --> don't care
  vector<int> onset_or_offset(sop_length, 2);
  vector<vector<int>> cube_idx_0, cube_idx_1;
  for (int i = 0 ; i < fanin0_sop.size() ; ++i)
  {
    vector<int> temp_idx;
    for (int j = 0 ; j < sop_length ; ++j)
    {
      if (fanin0_sop[i][j] == "0") { onset_or_offset[j] = 0; temp_idx.push_back(j); }
      else if (fanin0_sop[i][j] == "1") { onset_or_offset[j] = 1; temp_idx.push_back(j); }
    }
    cube_idx_0.push_back(temp_idx);
  }
  for (int i = 0 ; i < fanin1_sop.size() ; ++i)
  {
    vector<int> temp_idx;
    for (int j = 0 ; j < sop_length ; ++j)
    {
      if (fanin1_sop[i][j] == "0") { onset_or_offset[j] = 0; temp_idx.push_back(j); }
      else if (fanin1_sop[i][j] == "1") { onset_or_offset[j] = 1; temp_idx.push_back(j); }
    }
    cube_idx_1.push_back(temp_idx);
  }
  // 同 program.cc 作法, 先不管每個 lit 的 phase, 做 cart_product
  vector<vector<int>> temp_ans;
  for (int i = 0 ; i < fanin0_sop.size() ; ++i)
  {
    vector<vector<int>> cube_idx_0_temp = {cube_idx_0[i]};
    vector<vector<int>> cube_idx;
    cube_idx.insert(cube_idx.end(), cube_idx_0_temp.begin(), cube_idx_0_temp.end());
    cube_idx.insert(cube_idx.end(), cube_idx_1.begin(), cube_idx_1.end());
    
    Vvi output;
    Vi outputTemp;
    cart_product_sop(output, outputTemp, cube_idx.begin(), cube_idx.end());
    for (int j = 0 ; j < output.size() ; ++j)
    {
      temp_ans.push_back(output[j]);
    }
  }
  // refine "Vvi output"
  Vvi refined_sop;
  refined_sop = refine_cube_idx(temp_ans);
  // 將 output 轉成 char* pSop
  vector<char*> temp_sop;
  for (int i = 0 ; i < refined_sop.size() ; ++i)
  {
    string temp_ans(sop_length, '-');
    for (int j = 0 ; j < refined_sop[i].size() ; ++j)
    {
      if (onset_or_offset[refined_sop[i][j]] == 0) { temp_ans.replace(refined_sop[i][j], 1, "0"); }
      else if (onset_or_offset[refined_sop[i][j]] == 1) { temp_ans.replace(refined_sop[i][j], 1, "1"); }
    }
    temp_sop.push_back(temp_ans);
  }
  combined_sop = temp_sop;

}


void BuildSop(Aig_Man_t* pAig, Aig_Obj_t* swapped_node, vector<Aig_Obj_t*>& PI_node, int& sop_length)
{
  if (Aig_ObjIsTravIdCurrent(swapped_node)) { return; }
  // fMarkA = 0 --> 還不能合成為 Sop  ;  fMarkA = 1 or PI --> 可以合成做 Sop
  // 如果是 PI --> 可以合成 sop (注意 sop variable 順序)
  if (swapped_node->pFanin0 == NULL) 
  {
    // initialize
    string temp_sop(sop_length, '-');
    if (Aig_IsComplement(swapped_node)) { temp_sop.replace(PI_node.size(), 1, "0"); }
    else { temp_sop.replace(PI_node.size(), 1, "1"); }
    swapped_node->pSop.push_back(temp_sop.c_str());
    // mark traversed
    Aig_ObjSetTravIdCurrent(pAig, swapped_node);
    // mark sop-ed
    Aig_ObjSetMarkA(swapped_node);
    // 按照 traverse 順序依序加入 PI node --> 對應 sop variable 順序
    PI_node.push_back(swapped_node);
    return;
  }

  // 如果 child 都合成完了 --> 可以合成 sop (兩個 vector<char*> 合併)
  else if ((Aig_ObjIsMarkA(swapped_node->pFanin0) == 1) && (Aig_ObjIsMarkA(swapped_node->pFanin1) == 1))
  {
    // output phase 如果沒有 complement, 直接 return 往上走
    // 先將 fanin 有 complement 的情況處理 --> 才能將兩個 fanin 合併
    vector<char*> fanin0_sop = swapped_node->pFanin0->pSop;
    vector<char*> fanin1_sop = swapped_node->pFanin1->pSop;
    if (Aig_IsComplement(swapped_node->pFanin0))
    {
      if (swapped_node->pFanin0->pSop.size() == 1) { fanin0_sop = one_cube_complement(swapped_node->pFanin0->pSop, sop_length); }
      else if (swapped_node->pFanin0->pSop.size() > 1) { fanin0_sop = multi_cube_complement(swapped_node->pFanin0->pSop, sop_length); }
    }
    if (Aig_IsComplement(swapped_node->pFanin1))
    {
      if (swapped_node->pFanin1->pSop.size() == 1) { fanin1_sop = one_cube_complement(swapped_node->pFanin1->pSop, sop_length); }
      else if (swapped_node->pFanin1->pSop.size() > 1) { fanin1_sop = multi_cube_complement(swapped_node->pFanin1->pSop, sop_length); }
    }
    // 現在要將 fanin0_sop, fanin1_sop AND 起來 (不用管輸出 phase 因為會在下次他變成 fanin 時操作 inv, 但最後 PO 要管嗎 ?)
    vector<char*> combined_sop;
    combine_fanin_sop(combined_sop, fanin0_sop, fanin1_sop, sop_length);

    // 把上面合併完的結果存到 swapped_node->pSop
    swapped_node->pSop = combined_sop;

    // mark traversed
    Aig_ObjSetTravIdCurrent(pAig, swapped_node);
    // mark sop-ed
    Aig_ObjSetMarkA(swapped_node);
    return;
  }

  // 如果 child0 和 child1 都還沒合成 --> 繼續往 child0 traverse 
  else if (Aig_ObjIsMarkA(swapped_node->pFanin0) == 0)
  {
    BuildSop(pAig, swapped_node->pFanin0, PI_node, sop_length);
  }

  // 如果 child0 合成完但 child1 還沒, 且 child1 是 PI --> 往 child1 traverse 並直接合併到目前所有 cube
  else if ((Aig_ObjIsMarkA(swapped_node->pFanin0) == 1) && (Aig_ObjIsMarkA(swapped_node->pFanin1) == 0))
  {
    BuildSop(pAig, swapped_node->pFanin1, PI_node, sop_length);
  }

}



Abc_Obj_t* Lsv_NtkOrBidec(Abc_Obj_t* pObj, int max_fanin)
{
  // threshold fanin # > 0
  assert (max_fanin > 0);
  // initial variable 
    // duplicate the "object" not pointer
  Abc_Obj_t n_prime_obj = *pObj;
  Abc_Obj_t* n_prime = &n_prime_obj;
  int L = Abc_ObjFaninNum(pObj);
  // add the root node into root_node_list
  n_prime->root_node_list.push_back(pObj);
  if (pObj->fMarkA == 2) { return n_prime }
  // mark 不重複 collapse
  pObj->fMarkA = 2;
  // if not exceeds threshold fanin #
  for (int i = 0 ; i < pObj->vFanins.nSize ; ++i)
  {
    Abc_Obj_t* cur_node = Abc_ObjFanin(pObj, i);
    while (L <= max_fanin)
    {
      // if PI or multi-fanout 
      if ((Abc_ObjType(cur_node) == ABC_OBJ_PI) || \
          (Abc_ObjFanin0(cur_node)->vFanouts.nSize > 1))
      {
        // add the node into root_node_list
        n_prime->root_node_list.push_back(cur_node);
        // add the hierarchical version
        vector<Abc_Obj_t*> temp_node = {cur_node};
        n_prime->root_node_list_hierar.push_back(temp_node);
        break;
      }
      // if not PI and not multi-fanout
      else
      {
        int new_node_num = Abc_ObjFaninNum(cur_node);
        vector<Abc_Obj_t*> temp_node;
        for (int j = 0 ; j < new_node_num ; ++j)
        {
          temp_node.push_back(Abc_ObjFanin(cur_node, j));
        }
        // if exceeds threshold fanin # --> 存當前的 node
        if (L - 1 + new_node_num > max_fanin) 
        {  
          n_prime->root_node_list.push_back(cur_node);
          vector<Abc_Obj_t*> tmp = {cur_node};
          n_prime->root_node_list_hierar.push_back(tmp);
          break; 
        }
        else // substitution
        {
          // update L --> sub original node, plus new node #
          L = L - 1 + new_node_num; 
          // substitution --> add the node into root_node_list
            // no matter if all new node are PI or multi-fanout --> 加進 node_list, 要判斷是否 PI 等留給主函數
          for (int j = 0 ; j < temp_node.size() ; ++j)
          {
            n_prime->root_node_list.push_back(temp_node[j]);
          }
          // add the hierarchical version
          n_prime->root_node_list_hierar.push_back(temp_node);
          break;
        }
      }
    }
  }

  // Operation 1 : 從 root_node_list 建立一個新的 Ntk, 以這些 node 為 PI 建立出 Aig (Abc_NtkToDar)
  int sop_length = n_prime->root_node_list.size();
  Abc_Ntk_t* trans_pNtk = n_prime->pNtk;
  // PI's vFanins --> NULL ; 他小孩的 fanout 也要切斷
  for (int i = 1 ; i < n_prime->root_node_list.size() ; ++i)
  { 
    for (int j = 0 ; j < n_prime->root_node_list[i]->vFanins.nSize ; ++j)
    {
      Vec_IntClear(n_prime->root_node_list[i]->vFanins[j]->vFanouts);
    }
    Vec_IntClear(n_prime->root_node_list[i]->vFanins);
  }
  // 改 Abc_Ntk_t 的 vPis, vCis
  Vec_PtrClear(trans_pNtk->vPis);
  Vec_PtrClear(trans_pNtk->vCis);
  for (int i = 1 ; i < n_prime->root_node_list ; ++i)
  {
    Vec_PtrPush(trans_pNtk->vPis, n_prime->root_node_list[i]);
    Vec_PtrPush(trans_pNtk->vCis, n_prime->root_node_list[i]);
  }
  
  // Operation 2 : PI 為 Sop variable (不包含 root node), 依序往上爆出 output 的 Sop
  trans_pNtk = Abc_NtkStrash(trans_pNtk, 0, 1, 0);
    // pNtk --> pAig
  Aig_Man_t* pAig = Abc_NtkToDar(trans_pNtk, 0, 1);
    // swap child --> let leftest child be the deepest 
    // ??? assume only a PO ???
  Aig_Obj_t* swapped_node = pAig->Aig_ManCo(pAig, 0);
    // 從最底下開始往上合成 Sop
      // swapped_node --> Aig tree 的 root
      // cur_node --> 最左邊底下的 child (begin to build SOP)
  vector<char*> node_to_sop;
    // 這時呼叫函數輸出 vector<char*> node_to_sop (解答)
    // 全部 fmarkA 先 reset --> fmarkA 標記是否可以合成 sop
  Aig_Obj_t* pObj;
  vector<Aig_Obj_t*> PI_node; // 並藉由目前長度去算應該要將值 assign 到 sop 的第幾個變數
  int node = 0;
  Aig_ManForEachNode(pAig, pObj, node) { Aig_ObjClearMarkA(pObj); }
  Aig_ManIncrementTravId(pAig);
    // 不考慮 xor 這種雙層電路, 所以 level 最高為 2 ?
  BuildSop(pAig, swapped_node, PI_node, sop_length);
  node_to_sop = swapped_node->pSop;
  // 如果 output phase 為 neg, 記得先做 complement
  if (Aig_IsComplement(swapped_node))
  {
    if (swapped_node->pSop.size() == 1) { node_to_sop = one_cube_complement(swapped_node->pSop, sop_length); }
    else if (swapped_node->pSop.size() > 1) { node_to_sop = multi_cube_complement(swapped_node->pSop, sop_length); }
  }

  // Operation 3 : 將 Sop 存到 n_prime root node's "collapsed_sop"
  string ans_sop;
  for (int i = 0 ; i < node_to_sop.size() ; ++i)
  {
    string temp(node_to_sop[i]);
    string temp_str = temp + " 1\n";
    ans_sop.append(temp_str);
  }
    // string to char* 
  n_prime->collapsed_sop = ans_sop.c_str();

  // return collapsed node (pObj->root_node_list)
    // if n_prime -> root_node_list.size() > 0 --> 有 collapse 
  return n_prime;

}


// Define command function : LSV_CommandOrBidec
int LSV_CommandOrBidec(Abc_Frame_t* pAbc, int argc, char** argv)
{
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
  {
    switch (c)
    {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return -1;
  }
  // main function
  // global variable 
  cout << "=======================" << endl;
  cout << "argv[1] : " << argv[1] << endl;
  cout << "=======================" << endl;

  Abc_Obj_t* ntk_PO;
  int co_node;

  // For each Co, extract cone of each Co & support set (Co: Combinational output)
  Abc_NtkForEachCo(pNtk, ntk_PO, co_node)
  {
    Lsv_NtkOrBidec(ntk_PO, stoi(argv[1]));
  }
  // Lsv_NtkOrBidec(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_or_bidec [-h]\n");
  Abc_Print(-2, "\t        check the OR bi-decomposition in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;

}