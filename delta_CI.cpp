#include <math.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <iomanip>
#include <cassert>
#include <vector>
#include <string>
#include <deque>
#include <iostream>
#include <fstream>
#include <sstream>
using namespace std;

//Start from the initial node, use the breadth-first search algorithm to find all the target nodes 
void Find_TarNode(int N, int num, int Initial_node, deque< deque<int> > Neighbor, deque<int> *TarNode) {
    deque<int> Tar;
    deque<int> check;
    for (int i = 0; i < N; i++){
        check.push_back(0);
    }
    Tar.push_back(Initial_node);
    check[Initial_node] = 1;
    int iter = 0;
    do
    {
        for (int i = 0; i < Neighbor[Tar[iter]].size(); i++){
            if (check[Neighbor[Tar[iter]][i]] == 0)
            {
                Tar.push_back(Neighbor[Tar[iter]][i]);
                check[Neighbor[Tar[iter]][i]] = 1;
            }
        }
        iter++;
    } while ((int)Tar.size() < num);
    
    for (int i = 0; i < num; i++) {
        (*TarNode).push_back(Tar[i]);
    }
    return;
}

//Use the breadth-first search algorithm to get the subgraph of nodes 
deque<int> SubGraph(int N, deque<int> TarNode_center, deque< deque<int> > Neighbor, int P, int *queue, int *length){
    deque<int> check1;  
    deque<int> check2;  
    deque<int> subgraph;
    int *r, *w, temp, delta, cnt, k, neigh;
    int s;
    for(int i=0; i<N; i++){
        check1.push_back(0);
        check2.push_back(0);
    }
    for (int i = 0; i < TarNode_center.size(); i++) {
        r = queue;
        w = queue + 1;
        temp = 1;
        delta = 1;
        length[0] = 1;
        s = 1;
        cnt = 0;
        queue[0] = TarNode_center[i];
        if(check2[TarNode_center[i]]==0){
            subgraph.push_back(TarNode_center[i]);
            check2[TarNode_center[i]] = 1;
        }
        check1[TarNode_center[i]] = 1;
        while(r != w) {
            if(s <= P) {
                for(k = 0; k < Neighbor[*r].size(); k++) {
                    neigh=Neighbor[*r][k];
                    if (check1[neigh] == 0){
                        queue[temp++] = neigh;
                        check1[neigh] = 1;
                        length[s] += 1;
                        if(check2[neigh] == 0){
                            subgraph.push_back(neigh);
                            check2[neigh] = 1;
                        }
                    }
                }
            }
            r += 1;
            w += temp - delta;
            delta = temp;
            cnt += 1;
            if(cnt == length[s-1]) {
                s++;
                cnt = 0;
            }
        }
        for(int j=0; j<N; j++){
            check1[j] = 0;
        }
    }
    return subgraph;
}

//The generation process of complement subgraph excluding the target nodes
deque< deque<int> > Comp_SubGraph(int N, deque< deque<int> > Neighbor, deque<int> TarNode){
    int Node1, Node2;
    for (int i = 0; i < TarNode.size(); i++) {
        Node1=TarNode[i];
        for (int j = 0; j < Neighbor[Node1].size(); j++) {
            Node2=Neighbor[Node1][j];
            for (int k = 0; k < Neighbor[Node2].size(); k++) {
                if (Neighbor[Node2][k] == Node1) {
                    Neighbor[Node2].erase(Neighbor[Node2].begin()+k);
                    break;
                }
            }
        }
        Neighbor[Node1].clear();
    }
    return Neighbor;
}

//Collective Influence algorithm
double CI(int Node, deque< deque<int> > Neighbor, int L, int *queue, int *length, int *Noback_check){
    if (Neighbor[Node].size()==0) {
        return 0.0;
    }
    else{
        int *r, *w, temp, delta, cnt, k, neigh, index;
        int s;
        double CI;
        CI=0.0;
        Noback_check[Node] = 1;
        queue[0] = Node;
        r = queue;
        w = queue + 1;
        temp = 1;
        delta = 1;
        length[0] = 1;
        s = 1;
        cnt = 0;
        while(r != w) {
            if(s <= 2*L-1) {
                for(k = 0; k < Neighbor[*r].size(); k++) {
                    neigh=Neighbor[*r][k];
                    if (Noback_check[neigh] == 0)
                    {
                        queue[temp++] = neigh;
                        Noback_check[neigh] = 1;
                        length[s] += 1;
                    }
                }
            }
            r += 1;
            w += temp - delta;
            delta = temp;
            cnt += 1;
            if(cnt == length[s-1]) {
                s++;
                cnt = 0;
            }
        }
        index = 0;
        for(s = 0; s < 2*L-1; s++){
            index += length[s];
        }
        CI = 0.0;
        double sum_deg=0.0;
        for (int i = 0; i < length[2*L-1]; ++i)
        {
            sum_deg += ( Neighbor[queue[index+i]].size()-1 );
        }
        CI=(Neighbor[Node].size()-1)*sum_deg;
        for(k = 0; k < temp; k++){
            Noback_check[queue[k]] = 0;
        }
        for(s = 0; s <= 2*L-1; s++){
            length[s] = 0;
        }
        return CI;
    }
}

double module(int N, double *V){
    double max=0.0;
    for (int i=0; i<N; ++i) {
        max+=V[i]*V[i];
    }
    max=sqrt(max);
    return max;
}

void Set_Neighbor_Comp(int N, deque< deque<int> > Neighbor, deque<int> *comp, int compNumber, int currentNode){
    int temp = 1;
    int delta = 1;
    int neigh;
    int *queue, *read, *write;
    queue = (int *)calloc(N, sizeof(int));
    queue[0] = currentNode;
    read = queue;
    write = queue + 1;
    while(read != write) {
        for(int i = 0; i < Neighbor[*read].size(); i++) {
            neigh =  Neighbor[*read][i];
            if((*comp)[neigh] <= 0) {
                (*comp)[neigh] = compNumber;
                queue[temp] = neigh;
                temp += 1;
            }
        }
        read += 1;
        write += temp - delta;
        delta = temp;
    }
    free(queue);
    return;
}

//GCC
int Max_Size_largest_Comp(int N, deque<int> *comp, deque< deque<int> > Neighbor){
    int  compNumber, size_largest_comp, *Size_comp;
    int  largest_compNum;
    compNumber = 0;
    
    for(int i = 0; i < N; i++){
        (*comp)[i] = 0;
    }
    for(int i = 0; i < N; i++){
        if((*comp)[i] <= 0){
            compNumber++;
            (*comp)[i] = compNumber;
            Set_Neighbor_Comp(N, Neighbor, comp, compNumber, i);
        }
    }    
    Size_comp = (int *)calloc(compNumber+1, sizeof(int));    
    for (int i = 0; i < compNumber+1; ++i)
    {
        Size_comp[i]=0;
    }
    for(int i = 0; i < N; i++){
        Size_comp[(*comp)[i]] = Size_comp[(*comp)[i]]+1;
    }
    size_largest_comp = 0;
    largest_compNum=-1;
    for(int i = 1; i < compNumber+1; i++){
        if(size_largest_comp < Size_comp[i]){
        	size_largest_comp = Size_comp[i];
            largest_compNum=i;
        }
    }
    for (int i = 0; i < N; i++) {
        if ((*comp)[i] == largest_compNum) {
            (*comp)[i] = 1;
        }
        else{
            (*comp)[i] = 0;
        }
    }
    free(Size_comp);
    return size_largest_comp;
}

int main()
{
    srand((unsigned)time(NULL));
    int cla=7; //the scale of subgraph
    int l=1; //the parameter of Collective Influence algorithm
    double beta; //the probability that an infectious node will infect its susceptible neighbor
    int tar_cluster_num = 1; //number of clusters of target nodes
    
	//create an ER network
    int N = 10000; //size of network
    double mean_deg=4.0; //mean degree
    double p = mean_deg/(N-1);
    deque< deque<int> > Neighbor; //Neighbor List
    deque<int> comp;
    for(int i=0; i<N; i++){
        deque<int> iter1;
        Neighbor.push_back(iter1);
        int iter2 = 0;
        comp.push_back(iter2);
    }        
    double r;
    for(int i=0; i<N; i++){
        for(int j=i+1; j<N; j++){
            r=(double)rand()/RAND_MAX;
            if(r<p){
                Neighbor[i].push_back(j);
                Neighbor[j].push_back(i);
            }
        }
    }
    int MaxSize = Max_Size_largest_Comp(N, &comp, Neighbor); //size of GCC
            
    //target nodes 
    int N2 = 10;
    int N1=tar_cluster_num*N2;
    deque<int> tar_seed_node; //the set of all target nodes 
    int seed_node;
    deque<int> TarNode;
    deque<int> target_check;
    for(int i=0; i<N; i++){
        target_check.push_back(0);
    }
    for (int i = 0; i < tar_cluster_num; i++) {
        do{
            seed_node=rand()%N;
        }while( (int)Neighbor[seed_node].size() > 5 || comp[seed_node] == 0 || target_check[seed_node] == 1);
        tar_seed_node.push_back(seed_node);
        Find_TarNode(N, N2 , seed_node , Neighbor, &TarNode);
    	for(int j = 0; j < N2; j++){
            	target_check[TarNode[i*N2+j]]=1;
        	}
        }
            
    //The generation process of subgraph
    deque<int> Sub_Graph;
    int *queue_sub;
    int *length_sub;
    queue_sub = (int*)calloc(N, sizeof(int));
    length_sub = (int*)calloc(cla+1, sizeof(int));
    Sub_Graph = SubGraph(N, tar_seed_node, Neighbor, cla , queue_sub, length_sub);
    deque<int> NewGraph;
    deque<int> check;
    for(int i=0; i<N; i++){
        check.push_back(0);
    }
    for(int i=0; i<Sub_Graph.size(); i++){
        check[Sub_Graph[i]]=1;
    }
    for(int i=0; i<Sub_Graph.size(); i++){
        for(int j=i+1; j<Sub_Graph.size();j++){
            if(Sub_Graph[j]<Sub_Graph[i]){
                int iter;
                iter=Sub_Graph[j];
                Sub_Graph[j]=Sub_Graph[i];
                Sub_Graph[i]=iter;
            }
        }
    }
    for(int i=0; i<N; i++){
        NewGraph.push_back(-1);
    }
    for(int i=0; i<Sub_Graph.size(); i++){
        NewGraph[Sub_Graph[i]]=i;
    }    
    deque< deque<int> > NewGraph_Neighbor;
    for(int i=0; i<Sub_Graph.size(); i++){
        deque<int> iter;
        NewGraph_Neighbor.push_back(iter);
    }
    for(int i=0; i<N; i++){
        if (check[i]==1) {
            for(int j=0; j<Neighbor[i].size(); j++){
                if(check[Neighbor[i][j]]==1){
                    int Node1=i;
                    int Node2=Neighbor[i][j];
                    int NodeNew1=NewGraph[Node1];
                    int NodeNew2=NewGraph[Node2];
                    NewGraph_Neighbor[NodeNew1].push_back(NodeNew2);
                    NewGraph_Neighbor[NodeNew2].push_back(NodeNew1);
                }
            }
            check[i]=0;
        }
    }
            
    //Collective Influence
    int *queue_new;
    int *length_new;
    int *Noback_check_new;
    double CI_result;
    deque<double> CI_result_store;
    deque<int> id_store_old;
    queue_new = (int*)calloc(N, sizeof(int));
    Noback_check_new = (int*)calloc(N, sizeof(int));
    length_new = (int*)calloc(2*l+1, sizeof(int));
    
    for(int i=0; i < Sub_Graph.size(); i++){
        if(target_check[Sub_Graph[i]] == 0){
            CI_result = CI(i, NewGraph_Neighbor, l, queue_new, length_new, Noback_check_new);
            CI_result_store.push_back(CI_result);
            id_store_old.push_back(Sub_Graph[i]);
        }
    }
	            
    //Comp_SubGraph 
    deque< deque<int> > Comp_Neighbor=Comp_SubGraph(N, Neighbor, TarNode);
            
    //Delta_CI
    double CI_Comp;
    deque<double> CI_Comp_store;
    deque<int> id_store_Comp;        
    for(int i=0; i < Sub_Graph.size(); i++){
        if(target_check[Sub_Graph[i]] == 0){
            CI_Comp = CI(Sub_Graph[i], Comp_Neighbor, l, queue_new, length_new, Noback_check_new);
            CI_Comp_store.push_back(CI_Comp);
            id_store_Comp.push_back(Sub_Graph[i]);
        }
    }
    deque<double> CI_NewVSComp;
    for (int i = 0; i < CI_Comp_store.size(); i++) {
        CI_NewVSComp.push_back(CI_result_store[i]-CI_Comp_store[i]);
    }  

    //Sorting in descending order       
    for(int i = 0; i < CI_NewVSComp.size(); i++){
        for(int j=i+1; j < CI_NewVSComp.size(); j++){
            if(CI_NewVSComp[j] > CI_NewVSComp[i]){
                double iter;
                iter=CI_NewVSComp[j];
                CI_NewVSComp[j]=CI_NewVSComp[i];
                CI_NewVSComp[i]=iter;
                int id;
                id=id_store_Comp[j];
                id_store_Comp[j]=id_store_Comp[i];
                id_store_Comp[i]=id;
            }
        }
    }                    
    return 0;
}
