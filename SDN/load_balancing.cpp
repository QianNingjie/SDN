//
//  load_balancing.cpp
//  SDN
//
//  Created by 钱宁婕 on 17/7/17.
//  Copyright © 2017年 钱宁婕. All rights reserved.
//

#include <map>
#include <list>
#include <set>
#include <iostream>

using namespace std;


class Link
{
public:
    int src;
    int srcPort;
    int dst;
    int dstPort;
    double latency;
};

const int MAXM = 5000 + 50;
const int MAXN = 500 + 50;

class MaxFlowSolver
{
    
private:
    struct edge
    {
        int y,c,next;
        edge(){}
        edge(int y_,int c_,int n_){y=y_,c=c_,next=n_;}
    }e[MAXM * 4];
    int head[MAXN];
    int nn,mm;
    int d[MAXN],cont[MAXN],q[MAXN];
    int pre[MAXN],cur[MAXN];
    bool vis[MAXN];
    void bfs(int s)
    {
        int x,to,tail=1,front=0;
        for(int i=1;i<=nn;i++) vis[i]=cont[i]=0,cur[i]=head[i],d[i]=0x3fffffff;
        d[s]=0;cont[0]=1;q[0]=s;vis[s]=1;
        while(front<tail)
            for(int i=head[x=q[front++]];i!=-1;i=e[i].next)
                if(!vis[to=e[i].y] && e[i^1].c)
                {
                    d[to]=d[x]+1;
                    vis[to]=1;
                    q[tail++]=to;
                    cont[d[to]]++;
                }
    }
    int SAP(int s,int t)
    {
        if(s==t) return 0x7fffffff;
        bfs(t);pre[s]=-1;
        int ans=0,x=s,y,flow,back;
        while(d[s]<nn)
        {
            y=-1;
            for(int i=cur[x];i!=-1;i=e[i].next)
                if(e[i].c && d[x]==d[e[i].y]+1)
                {
                    y=e[i].y;
                    cur[x]=i;
                    break;
                }
            if(y!=-1)
            {
                pre[y]=x;x=y;
                if(x==t)
                {
                    flow=0x3fffffff;
                    for(y=pre[y];y!=-1;y=pre[y])
                        if(flow>=e[cur[y]].c) flow=e[cur[y]].c,back=y;
                    for(x=pre[x];x!=-1;x=pre[x])
                        e[cur[x]^1].c+=flow,e[cur[x]].c-=flow;
                    ans+=flow;x=back;
                }
            }
            else
            {
                y=nn;
                for(int i=head[x];i!=-1;i=e[i].next)
                    if(e[i].c && y>d[e[i].y])
                        y=d[e[i].y],cur[x]=i;
                cont[d[x]]--;
                if(cont[d[x]]==0) break;
                cont[d[x]=y+1]++;
                if(x!=s) x=pre[x];
            }
        }
        return ans;
    }
    void addLink(int x,int y,int c)
    {
        //printf("***%d %d %d\n",x,y,c);
        e[mm]=edge(y,c,head[x]);head[x]=mm++;
        e[mm]=edge(x,0,head[y]);head[y]=mm++;
    }
    
    int nodeNum, edgeNum;
    int destination;
    
    map<int, int>nodeTable;
    map<Link*, int>edgeTable;
    Link *edgeIndexTable[MAXM * 2];
    
    int flowSrc;
    int flowDst[MAXN], dstCnt;
    
    int src[MAXM * 2];
    int dst[MAXM * 2];
    int restCap[MAXM * 2];
    int bgCap[MAXM * 2];
    int used[MAXM * 2];
    
    void initGraph(int n)
    {
        for(int i=1;i<=n;i++)
            head[i] = -1;
        nn = n;
        mm = 0;
    }
    void findPath(int s,list<Link*>&path)
    {
        for(int i=head[s];~i;i=e[i].next)
            if((i&1) && e[i].c)
            {
                e[i].c--;
                findPath(e[i].y, path);
                path.push_back(edgeIndexTable[i >> 1]);
                return ;
            }
    }
    
public:
    void init(const map<int, set<Link*>> &links, int nodeNum_,
              const map<Link*, int>&linkCost, const map<Link*, int>&linkBg,
              const int flowSrc_, const list<int>&flowDst_)
    {
        nodeTable.clear();
        edgeTable.clear();
        nodeNum = 0;
        edgeNum = 0;
        for(auto x : links)
            for(auto y : x.second)
            {
                if(nodeTable.count(y->src)==0)
                    nodeTable[y->src] = ++nodeNum;
                if(nodeTable.count(y->dst)==0)
                    nodeTable[y->dst] = ++nodeNum;
                
                edgeIndexTable[edgeNum] = y;
                edgeTable[y] = edgeNum;
                
                src[edgeNum] = nodeTable[y->src];
                dst[edgeNum] = nodeTable[y->dst];
                
                edgeNum++;
            }
        for(auto x : linkCost)
            restCap[edgeTable[x.first]] = x.second;
        
        for(auto x : linkBg)
            bgCap[edgeTable[x.first]] = x.second;
        
        dstCnt = 0;
        for(auto x : flowDst_)
            flowDst[dstCnt++] = nodeTable[x];
        flowSrc = nodeTable[flowSrc_];
    }
    bool solve(int bandWidth, int threshold, int padding, list<list<Link*>>&flowPath, map<Link*, int>&linkLimit)
    {
        if(padding < 0)
        {
            initGraph(nodeNum + 1);
            for(int i=0;i<edgeNum;i++)
            {
                int rest = max(restCap[i] + padding - threshold, 0);
                addLink(src[i], dst[i], rest / bandWidth);   //单向边
            }
            int sink = nodeNum + 1;
            for(int i=0;i<dstCnt;i++)
                addLink(flowDst[i], sink, 1);
            int flow = SAP(flowSrc, sink);
            if(flow == dstCnt)
            {
                linkLimit.clear();
                for(int i=0;i<edgeNum;i++)
                {
                    int use = e[2 * i + 1].c * bandWidth + threshold;
                    int limit = max(0, use - restCap[i]);
                    if(limit)
                        linkLimit[edgeIndexTable[i]] = limit;
                }
                
                flowPath.clear();
                for(int i=0;i<dstCnt;i++)
                {
                    list<Link*>path;
                    findPath(flowDst[i], path);
                    flowPath.push_back(path);
                }
                return 1;
            }
            else
                return 0;
        }
        else
        {
            initGraph(nodeNum + 1);
            for(int i=0;i<edgeNum;i++)
            {
                int rest = restCap[i] + min(padding, bgCap[i]) - threshold;
                addLink(src[i], dst[i], rest / bandWidth);   //单向边
            }
            int sink = nodeNum + 1;
            for(int i=0;i<dstCnt;i++)
                addLink(flowDst[i], sink, 1);
            int flow = SAP(flowSrc, sink);
            if(flow == dstCnt)
            {
                linkLimit.clear();
                for(int i=0;i<edgeNum;i++)
                {
                    int use = e[2 * i + 1].c * bandWidth + threshold;
                    int limit = max(0, use - restCap[i]);
                    if(limit)
                        linkLimit[edgeIndexTable[i]] = limit;
                }
                
                flowPath.clear();
                for(int i=0;i<dstCnt;i++)
                {
                    list<Link*>path;path.clear();
                    findPath(flowDst[i], path);
                    flowPath.push_back(path);
                }
                return 1;
            }
            else
                return 0;
        }
    }
}g;



bool rearrangeFlow(const map<int, set<Link*>> &links, int nodeNum,
                   const map<Link*, int>&linkCost, const map<Link*, int>&linkBg,
                   int flowSrc, const list<int>&flowDst, int bandWidth, int threshold,
                   list<list<Link*>>&flowPath, map<Link*, int>&linkLimit)
//如果不需要限速 那么linkLimit为空
{
    int maxBandWidth = 0, minBandWidth = 0;
    for(auto x : linkBg)
        maxBandWidth = max(maxBandWidth, x.second);  //所有链路上背景流最大的
    for(auto x : linkCost)
        minBandWidth = max(minBandWidth, x.second);   //所有链路上剩余带宽最大的
    
    g.init(links, nodeNum, linkCost, linkBg, flowSrc, flowDst);
    
    if(!g.solve(bandWidth, threshold, maxBandWidth, flowPath, linkLimit))
        return 0;     //将所有非视频流全部限速 仍然不能安排这些流
    
    int l = -minBandWidth, r = maxBandWidth, mid;
    while(l < r)
    {
        mid = (l + r) / 2;
        if(g.solve(bandWidth, threshold, mid, flowPath, linkLimit))
            r = mid;
        else
            l = mid + 1;
    }
    cerr<<r<<endl;
    g.solve(bandWidth, threshold, r, flowPath, linkLimit);
    return 1;         //找到解
}

/*
 
 4 4                点数 边数
 3 100 4 100 2 1    src srcPort dst dstPort totCap usedCap
 3 200 6 200 4 2
 4 200 7 100 3 2
 6 200 7 200 8 6
 1                  汇点个数
 3                  汇点编号
 7                  源点编号
 2                  视频流带宽
 
 */



/*
 3 200 6 200
 6 200 7 200
 ****************
 3 200 6 200
 6 200 7 200
 ****************
 3 100 4 100
 4 200 7 100
 ****************
 3 100 4 100 : 1
 3 200 6 200 : 2
 4 200 7 100 : 1
 6 200 7 200 : 2
 
 每排星号上面对应一条路径
 最下面是需要限速的link
 
 */


Link lk[MAXM];
int main()
{
    freopen("/Users/ningjieqian/Documents/c++\ workspace/SDN/1.txt", "r", stdin);
    freopen("/Users/ningjieqian/Documents/c++\ workspace/SDN/lbout/1.out", "w", stdout);
    int n,m;
    scanf("%d%d",&n,&m);
    
    map<Link*, int>linkCost, linkBg;
    map<int, set<Link*>>links;
    for(int i=0;i<m;i++)
    {
        int a,b,c,d;
        scanf("%d%d%d%d",&a,&b,&c,&d);
        lk[i].src = a;
        lk[i].srcPort = b;
        lk[i].dst = c;
        lk[i].dstPort = d;
        links[a].insert(&lk[i]);
        scanf("%d%d",&a,&b);
        linkCost[&lk[i]] = a - b;
        linkBg[&lk[i]] = b;
    }
    list<int>flowSrc;
    int cnt;
    scanf("%d",&cnt);
    for(int i=0;i<cnt;i++)
    {
        int x;
        scanf("%d",&x);
        flowSrc.push_back(x);
    }
    int flowDst;
    scanf("%d",&flowDst);
    int bandWidth;
    scanf("%d",&bandWidth);
    list<list<Link*>>flowPath;
    map<Link*, int> linkLimit;
    rearrangeFlow(links, n,linkCost,linkBg,flowDst,flowSrc,bandWidth,0,flowPath, linkLimit);
    for(auto x : flowPath)    //路径
    {
        for(auto y : x)
            printf("%d %d %d %d\n",y->src,y->srcPort,y->dst,y->dstPort);
        printf("****************\n");
    }
    for(auto x : linkLimit)  //限速
    {
        Link *p = x.first;
        printf("%d %d %d %d : %d\n",p->src,p->srcPort,p->dst,p->dstPort,x.second);
    }
    return 0;
}
