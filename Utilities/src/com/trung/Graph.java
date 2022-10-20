package com.trung;

import com.wolfram.jlink.Expr;
import com.wolfram.jlink.MathLinkFactory;

import java.util.*;
import java.util.concurrent.atomic.AtomicReference;

public class Graph<T> implements Cloneable
{
    protected HashMap<T, HashSet<T>> Adjacency;
    private HashMap<T, HashSet<T>> InAdjacency;
    protected HashMap<T, HashMap<T, Double>> EdgeWeights;
    protected HashMap<T, Double> VertexWeights;
    private HashMap<T, T> vertexOrigin;
    protected HashMap ElementProperties = new HashMap();
    protected HashMap<String, Object> GraphProperties = new HashMap();

    public static <S> Graph<S> completeGraph(Collection<S> vs)
    {
        var res = new Graph<S>(vs, new HashSet<>());
        for (var v0 : vs)
            for (var v1 : vs)
                if (!v0.equals(v1))
                    res.addEdge(v0, v1);
        return res;
    }

    public static <S> Graph<S> relationGraph(Collection<S> col, BinaryFunction<S, S, Boolean> f)
    {
        var res = new Graph<S>();
        res.addVertices(col);
        for (var ele0 : col)
            for (var ele1 : col)
            {
                if (f.apply(ele0, ele1))
                    res.addEdge(ele0, ele1);
            }
        return res;
    }

    public Object getGraphProperty(String propName)
    {
        return this.GraphProperties.get(propName);
    }

    public void setGraphProperty(String propName, Object value)
    {
        this.GraphProperties.put(propName, value);
    }

    public Object getVertexProperty(T v, String proname)
    {
        return Utilities.getValue(this.ElementProperties, "VertexProperties", v, proname);
    }

    public void setVertexProperty(T v, String proname, Object value)
    {
        Utilities.insertValue(this.ElementProperties, new Object[]{"VertexProperties", v, proname}, value);
    }

    public Object getEdgeProperty(ArrayList<T> ed, String proname)
    {
        return this.getEdgeProperty(ed.get(0), ed.get(1), proname);
    }

    public Object getEdgeProperty(T v0, T v1, String proname)
    {
        var ed = new ArrayList<T>();
        ed.add(v0);
        ed.add(v1);
        return Utilities.getValue(this.ElementProperties, "EdgeProperties", ed, proname);
    }

    public void setEdgeProperty(ArrayList<T> ed, String proname, Object value)
    {
        this.setEdgeProperty(ed.get(0), ed.get(1), proname, value);
    }

    public void setEdgeProperty(T v0, T v1, String proname, Object value)
    {
        var ed = new ArrayList<>();
        ed.add(v0);
        ed.add(v1);
        Utilities.insertValue(this.ElementProperties, new Object[]{"EdgeProperties", ed, proname}, value);
    }

    public Expr convertToMGraph(HashMap<T, Expr> corres, Object... opts)
    {
        try
        {
            var vc = this.vertexCount();
            var loopbackLink = new LoopbackLink();
            loopbackLink.putFunction("List", vc);
            for (var v : this.vertexList())
                loopbackLink.put(corres.get(v));
            var mVs = loopbackLink.getExpr();
            var ec = this.edgeCount();
            loopbackLink.putFunction("List", ec);
            for (var ed : this.edgeList())
            {
                var v0 = corres.get(ed.get(0));
                var v1 = corres.get(ed.get(1));
                loopbackLink.putFunction("DirectedEdge", 2);
                loopbackLink.put(v0);
                loopbackLink.put(v1);
            }
            var eds = loopbackLink.getExpr();
            var optsar = new ArrayList<Expr>();
            if (opts != null)
                for (var exp : opts)
                    optsar.add((Expr) exp);
            loopbackLink.putFunction("Graph", 2 + optsar.size());
            loopbackLink.put(mVs);
            loopbackLink.put(eds);
            for (var exp : optsar)
                loopbackLink.put(exp);
            var res = loopbackLink.getExpr();
            return res;
        } catch (Exception e)
        {
            System.out.println(e.getMessage());
            throw new RuntimeException("Error");
        }
    }

    public int diameter()
    {
        Integer res = null;
        var vs = Utilities.makeArrayList(this.vertexList());
        var size = vs.size();
        var pi = new ProgressIndicator(0, size - 1);
        pi.setDelay(1000);
        pi.show();
        for (var i = 0; i <= size - 1; i++)
        {
            if (pi.Stopped)
                break;
            pi.setValue(i);
            var v = vs.get(i);
            var dists = graphDistance(v);
            var values = dists.values();
            var maxDist = Utilities.max(values, (x, y) -> x - y);
            if (res == null)
                res = maxDist;
            else if (res.intValue() < maxDist.intValue())
                res = maxDist;
        }
        return res;
    }

    public static <T> Graph<T> reverseGraph(Graph<T> g)
    {
        var res = new Graph<T>();
        for (var v : g.vertexList())
            res.addVertex(v);
        for (var ed : g.edgeList())
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            res.addEdge(v1, v0);
        }
        return res;
    }

    public HashMap<T, Integer> graphDistance(T v0)
    {
        var minDistance = new HashMap<T, Integer>();
        var stack = new Stack<T>();
        var inStack = new HashSet<T>();
        var before = new HashMap<T, T>();
        stack.push(v0);
        inStack.add(v0);
        minDistance.put(v0, 0);
        before.put(v0, null);
        while (!stack.isEmpty())
        {
            var topEle = stack.pop();
            var outVs = outGoingVertices(topEle);
            for (var v : outVs)
            {
                var inVs = inGoingVertices(v);
                int minDis;
                if (minDistance.containsKey(v))
                    minDis = minDistance.get(v);
                else
                {
                    minDis = minDistance.get(topEle) + 1;
                    minDistance.put(v, minDis);
                    before.put(v, topEle);
                }
                for (var w : inVs)
                {
                    if (minDistance.containsKey(w))
                    {
                        var aux = minDistance.get(w) + 1;
                        if (aux < minDis)
                        {
                            minDis = aux;
                            before.put(v, w);
                            minDistance.put(v, minDis);
                        }
                    }
                }
                if (!inStack.contains(v))
                {
                    stack.push(v);
                    inStack.add(v);
                }
            }
        }
        for (var v : this.vertexList())
            if (!minDistance.containsKey(v))
                minDistance.put(v, -1);
        return minDistance;
    }

    public ArrayList<T> shortestPath(T v0, T v1)
    {
        var edgeWeightf = new HashMap<ArrayList<T>, Double>();
        for (var ed : this.edgeList())
            edgeWeightf.put(ed, 1d);
        return shortestPath(v0, v1, edgeWeightf);
    }

    public ArrayList<T> shortestPath(T v0, T v1, UnaryFunction<ArrayList<T>, ? extends Number> edgeWeightf)
    {
        var edWf = new HashMap<ArrayList<T>, Double>();
        for (var ed : this.edgeList())
            edWf.put(ed, edgeWeightf.apply(ed).doubleValue());
        return shortestPath(v0, v1, edWf);
    }

    public ArrayList<T> shortestPath(T v0, T v1, HashMap<ArrayList<T>, ? extends Number> edgeWeightf)
    {
        var minDistance = new HashMap<T, Double>();
        var stack = new Stack<T>();
        var inStack = new HashSet<T>();
        var before = new HashMap<T, T>();
        stack.push(v0);
        inStack.add(v0);
        minDistance.put(v0, 0d);
        before.put(v0, null);
        while (!stack.isEmpty())
        {
            var topEle = stack.pop();
            if (topEle.equals(v1))
            {
                var res = new ArrayList<T>();
                var runningEle = topEle;
                while (runningEle != null)
                {
                    res.add(runningEle);
                    runningEle = before.get(runningEle);
                }
                return (ArrayList<T>) (Object) Utilities.reverse(res);
            }
            var outVs = outGoingVertices(topEle);
            for (var v : outVs)
            {
                var inVs = inGoingVertices(v);
                double minDis;
                if (minDistance.containsKey(v))
                    minDis = minDistance.get(v);
                else
                {
                    minDis = minDistance.get(topEle) + edgeWeightf.get(
                            NullFunction.createInstance(() ->
                            {
                                var aux = new ArrayList<T>();
                                aux.add(topEle);
                                aux.add(v);
                                return aux;
                            }).apply()
                    ).doubleValue();
                    minDistance.put(v, minDis);
                    before.put(v, topEle);
                }
                for (var w : inVs)
                {
                    if (minDistance.containsKey(w))
                    {
                        var aux = minDistance.get(w) + edgeWeightf.get(
                                NullFunction.createInstance(() ->
                                {
                                    var list = new ArrayList<T>();
                                    list.add(w);
                                    list.add(v);
                                    return list;
                                }).apply()
                        ).doubleValue();
                        if (aux < minDis)
                        {
                            minDis = aux;
                            before.put(v, w);
                            minDistance.put(v, minDis);
                        }
                    }
                }
                if (!inStack.contains(v))
                {
                    stack.push(v);
                    inStack.add(v);
                }
            }
        }
        return null;
    }

//    private static LoopbackLink loopbackLink;

    public static boolean initialize()
    {
//        Utilities.executeMathematicaCode("Options[Graph`pageRank]={\"Damping Factor\"->0.85,\"Step Number\"->0,\"Show Progress\"->True}");
//        try
//        {
//            loopbackLink = MathLinkFactory.createLoopbackLink();
//        } catch (Exception e)
//        {
//        }
        return true;
    }

    public static boolean isInitialized = initialize();

    public static boolean pageRankExecutionStopped = false;

    public static <T> HashMap<T, Double> pageRank(Graph<T> g, HashMap<String, Object> opts)
    {
        double d;
        double stepNum;
        {
            var aux = opts.get("Damping Factor");
            if (aux == null)
                d = 0.85d;
            else d = ((Number) aux).doubleValue();
        }
        {
            var aux = opts.get("Step Number");
            if (aux == null)
                stepNum = 0;
            else stepNum = ((Number) aux).intValue();
        }
        var showIndicator = true;
        {
            var aux = opts.get("Show Progress");
            if (aux != null)
                showIndicator = ((Boolean) aux).booleanValue();
        }
        var PR = new HashMap<T, ArrayList<Double>>();
        var N = g.vertexCount();
        var vs = g.vertexList();
        for (var v : vs)
        {
            PR.put(v, new ArrayList<>());
            PR.get(v).add(1d / N);
        }
        ProgressIndicator progress = null;
        if (showIndicator)
        {
            progress = new ProgressIndicator(1, stepNum);
            progress.setDelay(1000);
            progress.show();
        }
        var outWeights = new HashMap<T, Double>();
        for (var v : vs)
        {
            var outVs = g.outGoingVertices(v);
            var vWeight = 0d;
            for (var w : outVs)
            {
                var weight = g.getEdgeWeight(v, w);
                vWeight += weight;
            }
            outWeights.put(v, vWeight);
        }
        for (var t = 1; t <= stepNum; t++)
        {
            if (showIndicator)
            {
                if (progress.Stopped)
                    break;
                progress.setValue(t);
            }
            for (var v : vs)
            {
                var newValue = (1 - d) / N;
                var inVs = g.inGoingVertices(v);
                for (var w : inVs)
                {
                    newValue += (d * PR.get(w).get(0) * g.getEdgeWeight(w, v) / outWeights.get(w));
                }
                PR.get(v).add(newValue);
            }
            for (var v : vs)
                PR.get(v).remove(0);
        }
        var res = new HashMap<T, Double>();
        for (var v : vs)
            res.put(v, PR.get(v).get(0));
        return res;
    }

    public boolean isConnectedGraph()
    {
        if (this.vertexCount() <= 1)
            return true;
        var v = Utilities.getFirstElement(this.Adjacency.keySet());
        var compos = weaklyConnectedComponent(v);
        return compos.size() == this.vertexCount();
    }

    public static <T> HashMap<T, Double> randomWalk(Graph<T> g, int walkNum)
    {
        if (g.vertexCount() == 0)
            throw new RuntimeException("empty graph");
        var outgoingf = new HashMap<T, ArrayList<T>>();
        for (var v : g.vertexList())
        {
            outgoingf.put(v,
                    Utilities.makeArrayList(g.outGoingVertices(v))
            );
        }
        var res = new HashMap<T, Double>();
        var runningV = g.vertexList().iterator().next();
        BinaryAction<T, Double> increaseValue = (ele, value) ->
        {
            if (!res.containsKey(ele))
                res.put(ele, 0d);
            var currentValue = res.get(ele);
            res.put(ele, currentValue + value);
        };
        res.put(runningV, 1d);
        for (var i = 0; i <= walkNum - 2; i++)
        {
            var outVs = outgoingf.get(runningV);
            var selectedV = outVs.size() == 0 ? runningV : Utilities.randomChoice(outVs);
            increaseValue.apply(selectedV, 1d);
            runningV = selectedV;
        }
        for (var v : res.keySet())
            res.put(v, res.get(v) / walkNum);
        return res;
    }

    public boolean isStronglyConnected()
    {
        if (this.vertexCount() <= 1)
            return true;
        for (var v : this.Adjacency.keySet())
        {
            var outVs = this.vertexOutComponent(v);
            if (outVs.size() != this.vertexCount())
                return false;
        }
        return true;
    }

    public ArrayList<HashSet<T>> stronglyConnectedComponents()
    {
        var res = new ArrayList<HashSet<T>>();
        var index = new AtomicReference<Integer>();
        index.set(0);
        var vToIndex = new HashMap<T, Integer>();
        var vToLowlink = new HashMap<T, Integer>();
        var S = new Stack<T>();
        var onStack = new HashSet<T>();
        for (var v : vertexList())
            if (!vToIndex.containsKey(v))
                strongConnect(v, res, index, S, vToIndex, vToLowlink, onStack);
        return res;
    }

    private void strongConnect(T v, ArrayList<HashSet<T>> output,
                               AtomicReference<Integer> index,
                               Stack<T> S,
                               HashMap<T, Integer> vToIndex,
                               HashMap<T, Integer> vToLowlink,
                               HashSet<T> onStack)
    {
        vToIndex.put(v, index.get());
        vToLowlink.put(v, index.get());
        index.set(index.get() + 1);
        S.push(v);
        onStack.add(v);
        var outVs = outGoingVertices(v);
        for (var w : outVs)
        {
            if (!vToIndex.containsKey(w))
            {
                strongConnect(w, output, index, S, vToIndex, vToLowlink, onStack);
                vToLowlink.put(v, Math.min(vToLowlink.get(v), vToLowlink.get(w)));
            } else if (onStack.contains(w))
            {
                vToLowlink.put(v,
                        Math.min(vToLowlink.get(v), vToIndex.get(w))
                );
            }
        }
        if (vToLowlink.get(v).equals(vToIndex.get(v)))
        {
            var compos = new HashSet<T>();
            while (true)
            {
                var w = S.pop();
                onStack.remove(w);
                compos.add(w);
                if (w == v)
                    break;
            }
            output.add(compos);
        }
    }

    public HashSet<HashSet<T>> weaklyConnectedComponents()
    {
        var visitedEles = new HashSet<T>();
        var res = new HashSet<HashSet<T>>();
        for (var v : vertexList())
        {
            if (visitedEles.contains(v))
                continue;
            var vRes = weaklyConnectedComponent(v);
            res.add(vRes);
            visitedEles.addAll(vRes);
        }
        return res;
    }

    public HashSet<T> weaklyConnectedComponent(T v)
    {
        var res = new HashSet<T>();
        var stack = new Stack<T>();
        stack.push(v);
        while (!stack.isEmpty())
        {
            var topEle = stack.pop();
            res.add(topEle);
            var neighbors = new HashSet<T>();
            var outVs = outGoingVertices(topEle);
            var inVs = inGoingVertices(topEle);
            neighbors.addAll(outVs);
            neighbors.addAll(inVs);
            for (var w : neighbors)
                if (!res.contains(w))
                    stack.push(w);
        }
        return res;
    }

    /**
     * @return một chu trình trong đồ thị
     */
    public ArrayList<T> findCycle()
    {
        var visited = new HashMap<T, Boolean>();
        var finished = new HashMap<T, Boolean>();
        var before = new HashMap<T, T>();
        for (var v : vertexList())
        {
            var subRes = DFS(v, visited, finished, before);
            if (subRes != null)
                return subRes;
        }
        return null;
    }

    private ArrayList<T> DFS(T v, HashMap<T, Boolean> visited, HashMap<T, Boolean> finished, HashMap<T, T> before)
    {
        if (finished.containsKey(v) && finished.get(v) == true)
            return null;
        if (visited.containsKey(v) && visited.get(v) == true)
        {
            var res = new ArrayList<T>();
            res.add(v);
            var runningV = before.get(v);
            while (runningV != v)
            {
                res.add(runningV);
                runningV = before.get(runningV);
            }
            var reverseRes = new ArrayList<T>();
            for (var i = res.size() - 1; i >= 0; i--)
                reverseRes.add(res.get(i));
            return reverseRes;
        }
        visited.put(v, true);
        for (var w : outGoingVertices(v))
        {
            before.put(w, v);
            var subRes = DFS(w, visited, finished, before);
            if (subRes != null)
                return subRes;
        }
        finished.put(v, true);
        return null;
    }

    public int loopCount()
    {
        var res = 0;
        for (var v : this.Adjacency.keySet())
            for (var outV : this.Adjacency.get(v))
                if (v == outV)
                    res++;
        return res;
    }

    public T findLoop()
    {
        for (var v : this.Adjacency.keySet())
            for (var outV : this.Adjacency.get(v))
                if (v == outV)
                    return v;
        return null;
    }

    public boolean hasLoop()
    {
        for (var v : this.Adjacency.keySet())
            for (var outV : this.Adjacency.get(v))
                if (v == outV)
                    return true;
        return false;
    }

    public static <S> ArrayList<S> findPath(Graph<S> g, S v0, S v1)
    {
        return g.findPath(v0, v1);
    }

    public ArrayList<T> findPath(T v0, T v1)
    {
        var stack = new Stack<T>();
        var res = new ArrayList<T>();
        var before = new HashMap<T, T>();
        stack.push(v0);
        before.put(v0, null);
        while (!stack.isEmpty())
        {
            var topEle = stack.pop();
            if (topEle.equals(v1))
            {
                var runningEle = topEle;
                while (runningEle != null)
                {
                    res.add(0, runningEle);
                    runningEle = before.get(runningEle);
                }
                return res;
            } else
            {
                var outVs = this.outGoingVertices(topEle);
                for (var v : outVs)
                    if (!before.containsKey(v))
                    {
                        stack.push(v);
                        before.put(v, topEle);
                    }
            }
        }
        return null;
    }

    public static <T> Graph<T> vertexReplace(Graph<T> g, T v0, T v1)
    {
        var replaceMap = new HashMap<T, T>();
        replaceMap.put(v0, v1);
        return vertexReplace(g, replaceMap);
    }

    /**
     * @param replaceMap
     * @return trả lại đồ thị mà các đỉnh được thay thế bởi replaceMap
     */
    public static <T> Graph<T> vertexReplace(Graph<T> g, HashMap<T, T> replaceMap)
    {
        var res = g.clone();
        for (var v : replaceMap.keySet())
        {
            var inVs = res.inGoingVertices(v);
            inVs.remove(v);
            var outVs = res.outGoingVertices(v);
            outVs.remove(v);
            res.deleteVertex(v);
            var newV = replaceMap.get(v);
            res.addVertex(newV);
            for (var w : inVs)
                res.addEdge(w, newV);
            for (var w : outVs)
                res.addEdge(newV, w);
        }
        return res;
    }

    /**
     * @return trả lại số lượng cạnh của đồ thị này
     */
    public int edgeCount()
    {
        var res = 0;
        for (var v : this.Adjacency.keySet())
            res += this.Adjacency.get(v).size();
        return res;
    }

    public Graph<T> edgeInducedSubgraph(Collection<ArrayList<T>> eds)
    {
        var res = (Graph<T>) this.clone();
        var hs = new HashSet<ArrayList<T>>();
        hs.addAll(eds);
        res.deleteEdges((ed) -> !hs.contains(ed));
        return res;
    }


    public Graph<T> subgraph(Collection<T> vs)
    {
        var wVs = Utilities.makeHashSet(Utilities.select(vs,
                (x) -> this.containsVertex(x)
        ));
        var res = new Graph<T>();
        for (var v : wVs)
        {
            res.addVertex(vertexOrigin.get(v));
            if (this.VertexWeights.containsKey(v))
                res.setVertexWeight(v, this.VertexWeights.get(v));
            try
            {
                var vp = (HashMap) this.ElementProperties.get("VertexProperties");
                if (vp.containsKey(v))
                {
                    var hm = (HashMap<String, Object>) vp.get(v);
                    for (var proname : hm.keySet())
                        res.setVertexProperty(v, proname, hm.get(proname));
                }
            } catch (Exception e)
            {
            }
        }
        for (var s : wVs)
        {
            var outgoings = this.Adjacency.get(s);
            for (var t : outgoings)
            {
                if (wVs.contains(t))
                {
                    res.addEdge(s, t);
                    if (this.EdgeWeights.containsKey(s))
                        if (this.EdgeWeights.get(s).containsKey(t))
                            res.setEdgeWeight(s, t, this.EdgeWeights.get(s).get(t));
                    try
                    {
                        var eP = (HashMap) this.ElementProperties.get("EdgeProperties");
                        var ed = new ArrayList<T>();
                        ed.add(s);
                        ed.add(t);
                        if (eP.containsKey(ed))
                        {
                            var hm = (HashMap<String, Object>) eP.get(ed);
                            for (var proname : hm.keySet())
                                res.setEdgeProperty(ed, proname, hm.get(proname));
                        }
                    } catch (Exception e)
                    {
                    }
                }
            }
        }
        return res;
    }

    public boolean containsEdge(ArrayList<T> ed)
    {
        return this.containsEdge(ed.get(0), ed.get(1));
    }

    public boolean containsEdge(T v0, T v1)
    {
        if (this.Adjacency.containsKey(v0))
            return this.Adjacency.get(v0).contains(v1);
        else return false;
    }

    public boolean containsVertex(T v)
    {
        return this.Adjacency.containsKey(v);
    }

//    @Override
//    public Graph<T> clone()
//    {
//        var res = new Graph<T>();
//        this.clone(res);
//        return res;
//    }

    @Override
    public Graph<T> clone()
    {
        Graph<T> res = null;
        try
        {
            res = (Graph<T>) super.clone();
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }

        res.Adjacency = new HashMap<>();
        res.InAdjacency = new HashMap<>();
        res.EdgeWeights = new HashMap<>();
        res.VertexWeights = new HashMap<>();
        res.vertexOrigin = new HashMap<>();
        res.ElementProperties = new HashMap();
        res.GraphProperties = new HashMap<>();

        for (var v : this.Adjacency.keySet())
        {
            res.addVertex(v);
            if (this.VertexWeights.containsKey(v))
                res.setVertexWeight(v, this.VertexWeights.get(v));
        }
        for (var s : this.Adjacency.keySet())
        {
            for (var t : this.Adjacency.get(s))
                res.addEdge(s, t);
        }
        res.EdgeWeights = new HashMap<>();
        for (var v0 : this.EdgeWeights.keySet())
        {
            res.EdgeWeights.put(v0, new HashMap<T, Double>());
            for (var v1 : this.EdgeWeights.get(v0).keySet())
                res.EdgeWeights.get(v0).put(v1, this.EdgeWeights.get(v0).get(v1));
        }
        var originalProp = (HashMap<String, HashMap<Object, HashMap<String, Object>>>) this.ElementProperties;
        for (var proType : originalProp.keySet())
            for (var graphEle : originalProp.get(proType).keySet())
                for (var proName : originalProp.get(proType).get(graphEle).keySet())
                {
                    var value = originalProp.get(proType).get(graphEle).get(proName);
                    Utilities.insertValue(res.ElementProperties,
                            new Object[]{proType, graphEle, proName}, value
                    );
                }
        for (var propName : this.GraphProperties.keySet())
            res.setGraphProperty(propName, this.GraphProperties.get(propName));
        return res;
    }

    /**
     * @return trả lại số lượng đỉnh của đồ thị này
     */
    public int vertexCount()
    {
        return this.Adjacency.keySet().size();
    }

    public int vertexInDegree(T v)
    {
        return this.InAdjacency.get(v).size();
    }

    public int vertexOutDegree(T v)
    {
        return this.Adjacency.get(v).size();
    }

    public HashSet<T> vertexInComponent(T v, int radius)
    {
        var reverseG = reverseGraph(this);
        return reverseG.vertexOutComponent(v, radius);
    }

    public HashSet<T> vertexInComponent(T v)
    {
        var res = new HashSet<T>();
        var stack = new Stack<T>();
        stack.push(v);
        while (stack.size() > 0)
        {
            var topEle = stack.pop();
            res.add(topEle);
            var outs = this.InAdjacency.get(topEle);
            for (var w : outs)
                if (!res.contains(w))
                    stack.push(w);
        }
        return res;
    }

    public HashSet<T> vertexOutComponent(T v, int radius)
    {
        var dist = this.graphDistance(v);
        var res = new HashSet<T>();
        for (var s : dist.keySet())
        {
            var value = dist.get(s).intValue();
            if (value >= 0 && value <= radius)
                res.add(s);
        }
        return res;
    }

    public HashSet<T> vertexOutComponent(T v)
    {
        var res = new HashSet<T>();
        var stack = new Stack<T>();
        stack.push(v);
        while (stack.size() > 0)
        {
            var topEle = stack.pop();
            res.add(topEle);
            var outs = this.Adjacency.get(topEle);
            for (var w : outs)
                if (!res.contains(w))
                    stack.push(w);
        }
        return res;
    }

    public void deleteEdge(ArrayList<T> ed)
    {
        this.deleteEdge(ed.get(0), ed.get(1));
    }

    public void deleteEdges(Collection<ArrayList<T>> eds)
    {
        for (var ed : eds)
            this.deleteEdge(ed);
    }

    public void deleteEdges(UnaryFunction<ArrayList<T>, Boolean> crit)
    {
        var eds = this.edgeList();
        var deletedEds = new HashSet<ArrayList<T>>();
        for (var ed : eds)
            if (crit.apply(ed))
                deletedEds.add(ed);
        this.deleteEdges(deletedEds);
    }

    public void deleteEdge(T v0, T v1)
    {
        if (this.Adjacency.containsKey(v0))
            this.Adjacency.get(v0).remove(v1);
        if (this.InAdjacency.containsKey(v1))
            this.InAdjacency.get(v1).remove(v0);
        try
        {
            this.EdgeWeights.get(v0).remove(v1);
        } catch (Exception e)
        {
        }
        if (this.ElementProperties.containsKey(EdgeProperties))
        {
            var hm = (HashMap) this.ElementProperties.get(EdgeProperties);
            var ed = new ArrayList<T>();
            ed.add(v0);
            ed.add(v1);
            hm.remove(ed);
        }
    }

    public void deleteVertices(Collection<T> vs)
    {
        for (var v : vs)
            this.deleteVertex(v);
    }

    private final static String VertexProperties = "VertexProperties";
    private final static String EdgeProperties = "EdgeProperties";

    public void deleteVertices(UnaryFunction<T, Boolean> crit)
    {
        var vs = this.vertexList();
        var deletedVs = new HashSet<T>();
        for (var v : vs)
            if (crit.apply(v))
                deletedVs.add(v);
        this.deleteVertices(deletedVs);
    }

    public void deleteVertex(T v)
    {
        if (this.Adjacency.containsKey(v))
            this.Adjacency.remove(v);
        for (var w : this.Adjacency.keySet())
            this.Adjacency.get(w).remove(v);

        if (this.InAdjacency.containsKey(v))
            this.InAdjacency.remove(v);
        for (var w : this.InAdjacency.keySet())
            this.InAdjacency.get(w).remove(v);

        this.VertexWeights.remove(v);
        this.EdgeWeights.remove(v);
        for (var key : this.EdgeWeights.keySet())
            this.EdgeWeights.get(key).remove(v);

        if (this.ElementProperties.containsKey(VertexProperties))
            ((HashMap) this.ElementProperties.get(VertexProperties)).remove(v);

        this.vertexOrigin.remove(v);
    }

    public double getEdgeWeight(ArrayList<T> ed)
    {
        return this.getEdgeWeight(ed.get(0), ed.get(1));
    }

    public double getEdgeWeight(T v0, T v1)
    {
        return this.EdgeWeights.get(v0).get(v1);
    }

    public ArrayList<Double> getVertexWeights()
    {
        var res = new ArrayList<Double>();
        for (var v : this.vertexList())
        {
            var value = this.VertexWeights.containsKey(v) ? this.VertexWeights.get(v) : 0;
            res.add(value);
        }
        return res;
    }

    public ArrayList<Double> getEdgeWeights()
    {
        var edges = this.getEdges();
        var res = new ArrayList<Double>();
        for (var edge : edges)
        {
            var v0 = edge.get(0);
            var v1 = edge.get(1);
            try
            {
                var value = this.EdgeWeights.get(v0).get(v1);
                res.add(value == null ? 0 : value);
            } catch (Exception e)
            {
                res.add(0d);
            }
        }
        return res;
    }

    public HashSet<ArrayList<T>> edgeList()
    {
        return this.getEdges();
    }

    public HashSet<ArrayList<T>> getEdges()
    {
        var res = new HashSet<ArrayList<T>>();
        for (var v : this.Adjacency.keySet())
        {
            var outvs = this.Adjacency.get(v);
            for (var w : outvs)
            {
                var edge = new ArrayList<T>();
                edge.add(v);
                edge.add(w);
                res.add(edge);
            }
        }
        return res;
    }

    public HashSet<T> vertexList()
    {
        return this.getVertices();
    }

    public HashSet<T> getVertices()
    {
        var res = new HashSet<T>();
        for (var v : this.Adjacency.keySet())
            res.add(v);
        return res;
    }

    public <S extends Number> void setEdgeWeight(ArrayList<T> ed, S weight)
    {
        this.setEdgeWeight(ed.get(0), ed.get(1), weight);
    }

    public double getVertexWeight(T v)
    {
        return this.VertexWeights.get(v);
    }

    public <S extends Number> void setVertexWeight(T v, S weight)
    {
        var ov = this.vertexOrigin.get(v);
        this.VertexWeights.put(ov, weight.doubleValue());
    }

    public <S extends Number> void setEdgeWeight(T v0, T v1, S weight)
    {
        this.setEdgeWeight(v0, v1, weight.doubleValue());
    }

    public void setEdgeWeight(ArrayList<T> ed, double weight)
    {
        this.setEdgeWeight(ed.get(0), ed.get(1), weight);
    }

    public void setEdgeWeight(T v0, T v1, double weight)
    {
        if (this.Adjacency.containsKey(v0) && this.Adjacency.containsKey(v1))
        {
            var v00 = this.vertexOrigin.get(v0);
            var v11 = this.vertexOrigin.get(v1);
            if (!this.EdgeWeights.containsKey(v00))
                this.EdgeWeights.put(v00, new HashMap<>());
            this.EdgeWeights.get(v00).put(v11, weight);
        }
    }

    public HashSet<T> inGoingVertices(T v)
    {
        if (this.InAdjacency.containsKey(v))
            return Utilities.makeHashSet(this.InAdjacency.get(v));
        else return new HashSet<T>();
    }

    public HashSet<T> outGoingVertices(T v)
    {
        if (this.Adjacency.containsKey(v))
            return Utilities.makeHashSet(this.Adjacency.get(v));
        else return new HashSet<T>();
    }


    /**
     * bạn không cần phải thêm đỉnh vì hàm này sẽ tự động thêm đỉnh cho đồ thị nếu đỉnh vẫn chưa có
     * trong đồ thị
     *
     * @param edge
     */
    public void addEdge(ArrayList<T> edge)
    {
        var v0 = edge.get(0);
        var v1 = edge.get(1);
        this.addEdge(v0, v1);
    }

    public void addEdges(Collection<ArrayList<T>> eds)
    {
        for (var ed : eds)
            this.addEdge(ed);
    }

    /**
     * bạn không cần phải thêm đỉnh vì hàm này sẽ tự động thêm đỉnh cho đồ thị nếu đỉnh vẫn chưa có
     * trong đồ thị
     *
     * @param v0
     * @param v1
     */
    public void addEdge(T v0, T v1)
    {
        this.addVertex(v0);
        this.addVertex(v1);
        var v00 = this.vertexOrigin.get(v0);
        var v11 = this.vertexOrigin.get(v1);
        this.Adjacency.get(v00).add(v11);
        this.InAdjacency.get(v11).add(v00);
    }

    public void addVertices(Collection<T> vs)
    {
        for (var v : vs)
            this.addVertex(v);
    }

    public void addVertex(T v)
    {
        if (!this.Adjacency.containsKey(v))
        {
            this.Adjacency.put(v, new HashSet<>());
            this.InAdjacency.put(v, new HashSet<>());
            this.vertexOrigin.put(v, v);
        }
    }

    public Graph(Collection<T> vertices, Collection<ArrayList<T>> edges)
    {
        this.Adjacency = new HashMap<>();
        this.InAdjacency = new HashMap<>();
        this.EdgeWeights = new HashMap<>();
        this.vertexOrigin = new HashMap<>();
        this.VertexWeights = new HashMap<>();
        for (var v : vertices)
            this.addVertex(v);
        for (var ed : edges)
            this.addEdge(ed);
    }

    public Graph(Collection<ArrayList<T>> edges)
    {
        this.Adjacency = new HashMap<>();
        this.InAdjacency = new HashMap<>();
        this.EdgeWeights = new HashMap<>();
        this.VertexWeights = new HashMap<>();
        this.vertexOrigin = new HashMap<>();
        for (var ed : edges)
        {
            this.addVertex(ed.get(0));
            this.addVertex(ed.get(1));
            this.addEdge(ed);
        }
    }

    public Graph()
    {
        this.Adjacency = new HashMap<>();
        this.InAdjacency = new HashMap<>();
        this.EdgeWeights = new HashMap<>();
        this.VertexWeights = new HashMap<>();
        this.vertexOrigin = new HashMap<>();
    }

    @Override
    public String toString()
    {
        var vertices = new HashSet<>();
        var edges = new HashSet<>();
        for (var v : this.Adjacency.keySet())
        {
            vertices.add(v);
            var vs = this.Adjacency.get(v);
            for (var w : vs)
            {
                var edge = new ArrayList<>();
                edge.add(v);
                edge.add(w);
                edges.add(edge);
            }
        }
        return "Graph{" + "Vertices= " + vertices + ", " + "Edges= " + edges + "}";
    }
}
