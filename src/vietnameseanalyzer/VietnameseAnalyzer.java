package vietnameseanalyzer;

import com.trung.*;
import com.wolfram.jlink.Expr;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Function;

public class VietnameseAnalyzer
{
    public static boolean isEssentialOutsideTypeError(Graph<WordVertex> tree, WordVertex v)
    {
        if (!isWordOutside(tree, v))
            return false;
        var outsideTypes = getEssentialOutsideTypes();
        return !outsideTypes.contains(v.Type);
    }

    public static HashSet<String> EssentialOutsideTypes = null;

    public static HashSet<String> getEssentialOutsideTypes()
    {
        if (EssentialOutsideTypes != null)
            return EssentialOutsideTypes;
        var res = new HashMap<String, Integer>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
                if (isWordOutside(tree, v))
                    Utilities.insertValue(res,
                            new Object[]{v.Type}, 0, x -> x + 1
                    );
        }
        var mean = Utilities.mean(res.values());
        Utilities.removeKeys(res, x -> res.get(x) < mean);
        EssentialOutsideTypes = Utilities.makeHashSet(res.keySet());
        return EssentialOutsideTypes;
    }

    public static HashMap<String, Integer> RootTypeAppearances = null;

    public static HashMap<String, Integer> getRootTypeAppearances()
    {
        if (RootTypeAppearances != null)
            return RootTypeAppearances;
        var res = new HashMap<String, Integer>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
                if (tree.vertexOutDegree(v) == 0)
                    Utilities.insertValue(res,
                            new Object[]{v.Type}, 0, x -> x + 1
                    );
        }
        RootTypeAppearances = res;
        return res;
    }

    public static Graph<WordVertex> decideParser(String[][] wordInfos)
    {
        var length = wordInfos.length;
        var copiedArr = new String[length][];
        for (var i = 0; i <= length - 1; i++)
        {
            var iArr = new String[wordInfos[i].length];
            for (var j = 0; j <= wordInfos[i].length - 1; j++)
                iArr[j] = Utilities.normalizeText(wordInfos[i][j]);
            copiedArr[i] = iArr;
        }
        return decideParser(makeAnalyzingGraph(copiedArr));
    }

    public static Graph<WordVertex> decideParser(String sentence)
    {
        var jg = makeAnalyzingGraph(
                Utilities.normalizeText(sentence)
        );
        var preRes = decideParser(jg);
        var betterTree = findABetterType(jg, preRes);
        if (betterTree == null)
            return preRes;
        else return betterTree;
    }

    public static Parser decideParser(Graph<WordVertex> g)
    {
        var composes = g.weaklyConnectedComponents();
        if (composes.size() <= 1)
            return connectedDecideParser(g);
        else
        {
            var subParsers = Utilities.map(
                    compos ->
                    {
                        var subG = g.subgraph(compos);
                        return connectedDecideParser(subG);
                    }
                    , composes);
            Utilities.sortBy(subParsers,
                    parser ->
                    {
                        return Utilities.min(Utilities.map(x -> x.Location, parser.vertexList()));
                    }
            );
            var res = new Parser();
            Utilities.map(
                    parser ->
                    {
                        res.addVertices(parser.vertexList());
                        res.addEdges(parser.edgeList());
                    }
                    , subParsers);
            int type = -1;
            var maxLocs = Utilities.map(
                    (Parser x) ->
                    {
                        var vs = x.vertexList();
                        return Utilities.maxBy(vs, y -> y.Location).Location;
                    }
                    , subParsers);
            if (subParsers.size() == 1)
                type = 1;
            else if (Utilities.isOrdered(maxLocs, (x, y) -> x - y))
                type = 2;
            else type = 3;
            if (type == 1)
                return res;
            else if (type == 2)
            {
                var root0 = getRoot(subParsers.get(0));
                var root1 = getRoot(subParsers.get(1));
                var ed = new CustomArrayList<>(new WordVertex[]{root0, root1});
                res.addEdge(ed);
                res.MeaningSupplementEdges.add(ed);
                return res;
            } else
            {
                var firstParser = subParsers.get(0);
                var secondParser = subParsers.get(1);
                var minV = Utilities.minBy(secondParser.vertexList(),
                        x -> x.Location
                );
                var selectedVs = Utilities.select(firstParser.vertexList(),
                        x -> x.Location < minV.Location
                );
                var subParser = firstParser.subgraph(selectedVs);
                var topVs = Utilities.select(subParser.vertexList(),
                        x -> subParser.vertexOutDegree(x) == 0
                );
                var maxV = Utilities.maxBy(topVs, x -> x.Location);
                var meaningEds = new HashSet<ArrayList<WordVertex>>();
                Utilities.map(parser ->
                        {
                            var root = getRoot(parser);
                            var ed = new CustomArrayList<>(new WordVertex[]{root, maxV});
                            res.addEdge(ed);
                            meaningEds.add(ed);
                        }, Utilities.part(subParsers, 1, subParsers.size() - 1)
                );
                res.MeaningSupplementEdges.addAll(meaningEds);
                return res;
            }
        }
    }

    public static Parser connectedDecideParser(Graph<WordVertex> inputg)
    {
        var g = inputg.clone();
        var fixedEds = new HashSet<ArrayList<WordVertex>>();
        var finalStep = false;
        while (true)
        {
            var vs = g.vertexList();
            var rootTypeApps = getRootTypeAppearances();
            var vsGroups = NullFunction.createInstance(() ->
            {
                var aux = Utilities.gatherBy(
                        Utilities.select(vs, x -> g.vertexInComponent(x).size() == vs.size()),
                        (x, y) -> x.Type.equals(y.Type)
                );
                return Utilities.select(aux,
                        x ->
                        {
                            var eleX = Utilities.getFirstElement(x);
                            return rootTypeApps.containsKey(eleX.Type);
                        }
                );
            }).apply();
            if (vsGroups.size() == 0)
                throw new RuntimeException("unable to decide root");
            var selectedRoots = findQuickMinimal(vsGroups,
                    (x, y) ->
                    {
                        var eleX = Utilities.getFirstElement(x);
                        var eleY = Utilities.getFirstElement(y);
                        return -(rootTypeApps.get(eleX.Type) - rootTypeApps.get(eleY.Type));
                    }
            );
            var trees = Utilities.map(
                    root ->
                    {
                        return maximumSpanningTree(g, root);
                    }
                    , selectedRoots);
            if (finalStep)
            {
                return new Parser(findQuickMinimal(trees,
                        (x, y) -> errorTreeCompare(x, y)
                ));
            }
            var counter = new HashMap<ArrayList<WordVertex>, Integer>();
            for (var tree : trees)
            {
                for (var ed : tree.edgeList())
                    Utilities.insertValue(counter,
                            new Object[]{ed}, 0, x -> x + 1
                    );
            }
            Utilities.removeKeys(counter,
                    x -> fixedEds.contains(x)
            );
            if (counter.keySet().size() == 0)
            {
                finalStep = true;
                g.deleteEdges(g.edgeList());
                g.addEdges(fixedEds);
                continue;
            }
            var maxValue = Utilities.max(counter.values());
            Utilities.removeKeys(counter,
                    x -> counter.get(x) < maxValue
            );
            fixedEds.addAll(counter.keySet());
            g.deleteEdges(g.edgeList());
            Utilities.map(
                    tree ->
                    {
                        g.addEdges(tree.edgeList());
                    }, trees);
            g.deleteEdges((ed) ->
            {
                return !fixedEds.contains(ed) && Utilities.anyTrue(fixedEds,
                        y -> y.get(0).equals(ed.get(0))
                );
            });
        }
    }

    public static double getEdgeWeight(ArrayList<WordVertex> ed)
    {
        return getEdgeWeight(ed.get(0), ed.get(1));
    }

    public static double getEdgeWeight(WordVertex v0, WordVertex v1)
    {
        var g = new Graph<WordVertex>();
        g.addEdge(v0, v1);
        return getTreeWeight(g);
    }

    public static double getTreeWeight(Graph<WordVertex> tree)
    {
        var ls = getWordAppearancesToEdgeWeightLeastSquare();
        var wordApps = getWordAppearances();
        final var incomingStr = "incoming";
        final var outcomingStr = "outcoming";
        return Utilities.sum(
                (ArrayList<WordVertex> ed) ->
                {
                    var v0 = ed.get(0);
                    var v1 = ed.get(1);
                    var dir = getEdgeDirection(ed);
                    var counter = WordAppearancesToEdgeWeightCounter;
                    var v0Assoc = (HashMap<String, Integer>) NullFunction.createInstance(() ->
                    {
                        var aux = Utilities.getValue(counter,
                                new CustomArrayList<>(new String[]{v0.Word, v0.Type}),
                                outcomingStr, dir
                        );
                        if (aux != null)
                            return aux;
                        else return new HashMap<>();
                    }).apply();
                    var v0Weight = Utilities.sum(
                            x -> isSimilarType(x, v1.Type) ? v0Assoc.get(x) : 0
                            , v0Assoc.keySet());
                    var v1Assoc = (HashMap<String, Integer>) NullFunction.createInstance(() ->
                    {
                        var aux = Utilities.getValue(counter,
                                new CustomArrayList<>(new String[]{v1.Word, v1.Type}), incomingStr,
                                dir
                        );
                        if (aux != null)
                            return aux;
                        else return new HashMap<>();
                    }).apply();
                    var v1Weight = Utilities.sum(
                            x -> isSimilarType(x, v0.Type) ? v1Assoc.get(x) : 0
                            , v1Assoc.keySet());
                    var app0 = wordApps.get(v0.Word).get(v0.Type);
                    var app1 = wordApps.get(v1.Word).get(v1.Type);
                    var prods = Utilities.mapThread((x, y) -> x.doubleValue() * y.doubleValue(),
                            ls,
                            (ArrayList<Number>) Utilities.toArrayList(new Number[]{
                                    app0,
                                    app1,
                                    v0Weight,
                                    v1Weight
                            })
                    );
                    return Utilities.sum(prods);
                }
                , tree.edgeList());
    }

    public static HashMap<ArrayList<String>, HashMap<String, HashMap<String, HashMap<String, Integer>>>> WordAppearancesToEdgeWeightCounter = null;
    public static ArrayList<Double> WordAppearancesToEdgeWeightLeastSquare = null;

    public static ArrayList<Double> getWordAppearancesToEdgeWeightLeastSquare()
    {
        if (WordAppearancesToEdgeWeightLeastSquare != null)
            return WordAppearancesToEdgeWeightLeastSquare;
        HashMap<ArrayList<String>, HashMap<String, HashMap<String, HashMap<String, Integer>>>> counter = new HashMap<>();
        WordAppearancesToEdgeWeightCounter = counter;
        final var incomingStr = "incoming";
        final var outcomingStr = "outcoming";
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var ed : tree.edgeList())
            {
                var dir = getEdgeDirection(ed);
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                Utilities.insertValue(counter,
                        new Object[]{new CustomArrayList<>(new String[]{v0.Word, v0.Type}), outcomingStr, dir,
                                v1.Type}, 0, x -> x + 1
                );
                Utilities.insertValue(counter,
                        new Object[]{
                                new CustomArrayList<>(new String[]{v1.Word, v1.Type}), incomingStr, dir, v0.Type
                        }, 0, x -> x + 1
                );
            }
        }
        var wordApps = getWordAppearances();
        var data = new ArrayList<ArrayList<Number>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var ed : tree.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var dir = getEdgeDirection(ed);
                var v0Assoc = (HashMap<String, Integer>) Utilities.getValue(counter,
                        new CustomArrayList<>(new String[]{v0.Word, v0.Type}),
                        outcomingStr, dir
                );
                var v0Weight = Utilities.sum(
                        x -> isSimilarType(x, v1.Type) ? v0Assoc.get(x) : 0
                        , v0Assoc.keySet());
                var v1Assoc = (HashMap<String, Integer>) Utilities.getValue(counter,
                        new CustomArrayList<>(new String[]{v1.Word, v1.Type}), incomingStr,
                        dir
                );
                var v1Weight = Utilities.sum(
                        x -> isSimilarType(x, v0.Type) ? v1Assoc.get(x) : 0
                        , v1Assoc.keySet());
                data.add(
                        new CustomArrayList<Number>(
                                new Double[]{
                                        wordApps.get(v0.Word).get(v0.Type).doubleValue(),
                                        wordApps.get(v1.Word).get(v1.Type).doubleValue(),
                                        v0Weight,
                                        v1Weight,
                                        Utilities.max(v0Weight, v1Weight)
                                }
                        )
                );
            }
        }
        WordAppearancesToEdgeWeightLeastSquare = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        return WordAppearancesToEdgeWeightLeastSquare;
    }

    public static ArrayList<Double> EndingNextBeforeLeastSquare = null;

    public static ArrayList<Double> getEndingNextBeforeLeastSquare()
    {
        if (EndingNextBeforeLeastSquare != null)
            return EndingNextBeforeLeastSquare;
        EndingNextBeforeLeastSquare = getNextBeforeLeastSquare(
                (tree, x, y) ->
                {
                    var vs = tree.vertexList();
                    return !Utilities.anyTrue(vs, v -> v.Location > y.Location);
                }
        );
        return EndingNextBeforeLeastSquare;
    }

    public static ArrayList<Double> StartingNextBeforeLeastSquare = null;

    public static ArrayList<Double> getStartingNextBeforeLeastSquare()
    {
        if (StartingNextBeforeLeastSquare != null)
            return StartingNextBeforeLeastSquare;
        StartingNextBeforeLeastSquare = getNextBeforeLeastSquare(
                (tree, x, y) ->
                {
                    var vs = tree.vertexList();
                    return !Utilities.anyTrue(vs, v -> v.Location < x.Location);
                }
        );
        return StartingNextBeforeLeastSquare;
    }

    public static ArrayList<Double> NextBeforeLeastSquare = null;

    public static ArrayList<Double> getNextBeforeLeastSquare()
    {
        if (NextBeforeLeastSquare != null)
            return NextBeforeLeastSquare;
//        var eds = new AtomicReference<HashSet<ArrayList<WordVertex>>>();
//        eds.set(null);
        NextBeforeLeastSquare = getNextBeforeLeastSquare(
                (tree, x, y) ->
                {
                    return true;
//                    if (eds.get() == null)
//                        eds.set(tree.edgeList());
//                    return Utilities.anyTrue(eds.get(),
//                            ed -> ed.contains(x) && ed.contains(y)
//                    );
                }
        );
        return NextBeforeLeastSquare;
    }

    public static ArrayList<Double> getNextBeforeLeastSquare(TernaryFunction<Graph<WordVertex>, WordVertex, WordVertex, Boolean> checkf)
    {
        var nextTypes = getNextTypes();
        var beforeTypes = getBeforeTypes();
        var wordApps = getWordAppearances();
        var data = new ArrayList<ArrayList<? extends Number>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            var vs = Utilities.makeArrayList(tree.vertexList());
            Utilities.sortBy(vs, x -> x.Location);
            for (var i = 0; i <= vs.size() - 2; i++)
            {
                var iV = vs.get(i);
                var nextIV = vs.get(i + 1);
                if (nextIV.Location - iV.Location == 1 && checkf.apply(tree, iV, nextIV))
                {
                    var nextWeight = NullFunction.createInstance(() ->
                    {
                        var corres = nextTypes.get(iV.Word).get(iV.Type);
                        return Utilities.sum(
                                x -> isSimilarType(x, nextIV.Type) ? corres.get(x) : 0
                                , corres.keySet());
                    }).apply();
                    var beforeWeight = NullFunction.createInstance(() ->
                    {
                        var corres = beforeTypes.get(nextIV.Word).get(nextIV.Type);
                        return Utilities.sum(
                                x -> isSimilarType(x, iV.Type) ? corres.get(x) : 0
                                , corres.keySet());
                    }).apply();
                    data.add(
                            new CustomArrayList<>(new Number[]{
                                    wordApps.get(iV.Word).get(iV.Type),
                                    wordApps.get(nextIV.Word).get(nextIV.Type),
                                    nextWeight, beforeWeight,
                                    Utilities.min(nextWeight, beforeWeight)
                                    /*(nextWeight+beforeWeight)/2*/
                            })
                    );
                }
            }
        }
        return getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
    }

    public static Graph<WordVertex> makeAnalyzingGraph(String[][] wordInfos)
    {
        return makeAnalyzingGraph(analyzeSentence(wordInfos));
    }

    public static Graph<WordVertex> makeAnalyzingGraph(String sentence)
    {
        return makeAnalyzingGraph(analyzeSentence(sentence));
    }

    public static Graph<WordVertex> makeAnalyzingGraph(ArrayList<ArrayList<SegmentWord>> segWordsGroups)
    {
//        var segWordsGroups = analyzeSentence(sentence);
        var toWordVerticesGroups = new ArrayList<ArrayList<WordVertex>>();
        var runningIndex = 0;
        for (var segWordsGroup : segWordsGroups)
        {
            var wordVericesGr = new ArrayList<WordVertex>();
            for (var word : segWordsGroup)
            {
                wordVericesGr.add(new WordVertex(runningIndex, word.Word, word.Type));
                runningIndex++;
            }
            toWordVerticesGroups.add(wordVericesGr);
        }
        var g = new Graph<WordVertex>();
        Utilities.map(x ->
        {
            g.addVertices(x);
        }, toWordVerticesGroups);
//        final var meaningTypeStr = "MeaningSeparationType";
        switch (toWordVerticesGroups.size())
        {
            case 1:
                g.addEdges(
                        Graph.completeGraph(toWordVerticesGroups.get(0)).edgeList()
                );
//                g.setGraphProperty(meaningTypeStr, 1);
                break;
            case 2:
                Utilities.map(
                        x ->
                        {
                            g.addEdges(Graph.completeGraph(x).edgeList());
                        }
                        , toWordVerticesGroups);
//                g.setGraphProperty(meaningTypeStr, 2);
                break;
            default:
                Utilities.map(
                        x ->
                        {
                            g.addEdges(Graph.completeGraph(x).edgeList());
                        }
                        , toWordVerticesGroups);
            {
                var prod = Utilities.cartesianProduct(
                        toWordVerticesGroups.get(0),
                        Utilities.getLastElement(toWordVerticesGroups));
                g.addEdges(prod);
                prod = Utilities.cartesianProduct(
                        Utilities.getLastElement(toWordVerticesGroups),
                        toWordVerticesGroups.get(0));
                g.addEdges(prod);
//                g.setGraphProperty(meaningTypeStr, 3);
            }
            break;
        }
        return g;
    }

    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> WordNextWords = null;

    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> getWordNextWords()
    {
        if (WordNextWords != null)
            return WordNextWords;
        var res = new HashMap<ArrayList<String>, HashSet<ArrayList<String>>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            var vs = Utilities.makeArrayList(tree.vertexList());
            Utilities.sortBy(vs, x -> x.Location);
            for (var i = 0; i <= vs.size() - 2; i++)
            {
                var iEle = vs.get(i);
                var nextIEle = vs.get(i + 1);
                if (nextIEle.Location - iEle.Location == 1)
                {
                    Utilities.insertValue(res,
                            new Object[]{
                                    new CustomArrayList<>(new String[]{iEle.Word, iEle.Type})
                            }, new HashSet<ArrayList<String>>(),
                            x ->
                            {
                                x.add(new CustomArrayList<>(new String[]{nextIEle.Word, nextIEle.Type}));
                                return x;
                            }
                    );
                }
            }
        }
        WordNextWords = res;
        return res;
    }

    public static String normalizeWord(String word)
    {
        var chars = Utilities.map(
                (Integer i) -> word.charAt(i)
                , Utilities.range(0, word.length() - 1));
        var map = new CustomHashMap<List<Character>, List<Character>>(
                new Object[][]{
                        {
                                new CustomArrayList<>(new Object[]{' ', ' '}),
                                new CustomArrayList<>(new Object[]{' '})
                        }
                }
        );
        chars = Utilities.rewrite(chars, map);
        chars = (ArrayList<Character>) Utilities.trim(chars, x -> x.equals(' '));
        var res = new AtomicReference<String>("");
        Utilities.map((Character c) ->
        {
            res.set(res.get() + c);
        }, chars);
        return res.get();
    }

    public static ArrayList<ArrayList<SegmentWord>> analyzeSentence(String[][] wordInfos)
    {
        var res = new ArrayList<ArrayList<SegmentWord>>();
        var runningPart = new ArrayList<SegmentWord>();
        var currentIndex = 0;
        for (var pair : wordInfos)
        {
            var word = normalizeWord(pair[0]);
            var type = normalizeWord(pair[1]);
            if (!word.equals(",") && word.length() > 0)
            {
                var size = word.split("\\s").length;
                var segWord = new SegmentWord(word, type,
                        currentIndex, currentIndex + size - 1);
                runningPart.add(segWord);
                currentIndex += size;
            } else if (word.equals(","))
            {
                if (runningPart.size() > 0)
                {
                    res.add(runningPart);
                    runningPart = new ArrayList<>();
                }
            }
        }
        if (runningPart.size() > 0)
            res.add(runningPart);
        return res;
    }

    public static ArrayList<ArrayList<SegmentWord>> analyzeSentence(String sentence)
    {
        var chars = Utilities.map(
                (Integer i) -> sentence.charAt(i)
                , Utilities.range(0, sentence.length() - 1));
        var selectedChars = Utilities.rewrite(chars,
                NullFunction.createInstance(() ->
                {
                    var aux = new HashMap<List<Character>, List<Character>>();
                    aux.put(
                            new CustomArrayList<>(new Character[]{' ', ' '}),
                            new CustomArrayList<>(new Character[]{' '})
                    );
                    aux.put(
                            new CustomArrayList<>(new Character[]{',', ','}),
                            new CustomArrayList<>(new Character[]{','})
                    );
                    aux.put(
                            new CustomArrayList<>(new Character[]{' ', ','}),
                            new CustomArrayList<>(new Character[]{','})
                    );
                    aux.put(
                            new CustomArrayList<>(new Character[]{'?'}),
                            new CustomArrayList<>(new Character[]{})
                    );
                    aux.put(
                            new CustomArrayList<>(new Character[]{'.'}),
                            new CustomArrayList<>(new Character[]{})
                    );
                    return aux;
                }).apply()
        );
        selectedChars = Utilities.rewrite(selectedChars,
                (List<Character> x) -> x.size() == 2 && x.get(0).equals(',') && !x.get(1).equals(' '),
                x -> new CustomArrayList<>(new Character[]{',', ' ', x.get(1)})
        );
        selectedChars = (ArrayList<Character>) Utilities.trim(selectedChars,
                x -> x.equals(' ') || x.equals(',')
        );
        var simplifiedS = "";
        for (var ele : selectedChars)
            simplifiedS += ele;
        var splits = simplifiedS.split(",");
        var subReses = Utilities.map(
                (String x) -> nonCommaAnalyzeSentence(x)
                , splits);
        var currentIndex = 0;
        for (var subRes : subReses)
        {
            for (var word : subRes)
            {
                word.Start += currentIndex;
                word.End += currentIndex;
            }
            currentIndex = Utilities.getLastElement(subRes).End + 1;
        }
        return subReses;
    }

    public static ArrayList<SegmentWord> nonCommaAnalyzeSentence(String sentence)
    {
        var res = preNonCommaAnalyzeSentence(sentence);
        var splitTypes = new String[]{"V", "E"};
        if (!Utilities.anyTrue(res, x -> Utilities.memberQ(splitTypes, x.Type)))
            return res;
        else
        {
            var wordApps = getWordAppearances();
            var EVVs = NullFunction.createInstance(() ->
            {
                var aux = Utilities.makeHashSet(Utilities.select(res,
                        x -> Utilities.memberQ(splitTypes, x.Type)
                ));
                var maxEle = Utilities.maxBy(aux,
                        x -> wordApps.get(x.Word).get(x.Type)
                );
                var auxRes = new HashSet<SegmentWord>();
                auxRes.add(maxEle);
                return auxRes;
            }).apply();
            var segArrays = new ArrayList<ArrayList<SegmentWord>>();
            var ar = new ArrayList<SegmentWord>();
            for (var segWord : res)
            {
                if (EVVs.contains(segWord))
                {
                    segArrays.add(ar);
                    segArrays.add(new CustomArrayList<>(new SegmentWord[]{segWord}));
                    ar = new ArrayList<>();
                } else ar.add(segWord);
            }
            segArrays.add(ar);
            var subReses = Utilities.map(
                    (ArrayList<SegmentWord> segArray) ->
                    {
                        if (segArray.size() == 0)
                            return segArray;
                        if (segArray.size() == 1 && Utilities.isIntersecting(EVVs, segArray))
                            return segArray;
                        var jointWord = "";
                        for (var i = 0; i <= segArray.size() - 1; i++)
                        {
                            if (i > 0)
                                jointWord += " ";
                            jointWord += segArray.get(i).Word;
                        }
//                        System.out.println(jointWord);
                        return nonCommaAnalyzeSentence(jointWord);
                    }
                    , segArrays);
            var mainRes = NullFunction.createInstance(() ->
            {
                var aux = new ArrayList<SegmentWord>();
                for (var ele : subReses)
                    aux.addAll(ele);
                return aux;
            }).apply();
            var currentIndex = 0;
            for (var segWord : mainRes)
            {
                var start = segWord.Start;
                var end = segWord.End;
                segWord.Start = currentIndex;
                segWord.End = currentIndex + (end - start);
                currentIndex = segWord.End + 1;
            }
            return mainRes;
        }
    }

    public static ArrayList<SegmentWord> preNonCommaAnalyzeSentence(String sentence)
    {
        var words = NullFunction.createInstance(() ->
        {
            var aux = (ArrayList<String>) Utilities.toArrayList(sentence.split("\\s"));
            return Utilities.select(aux,
                    x -> x.length() != 0
            );
        }).apply();
        var vs = new HashSet<SegmentWord>();
        var wordAppearances = getWordAppearances();
        for (var i = 0; i <= words.size() - 1; i++)
            for (var j = i; j <= words.size() - 1; j++)
            {
                var subWords = Utilities.part(words, i, j);
                var joinWord = "";
                for (var k = 0; k <= subWords.size() - 1; k++)
                {
                    if (k > 0)
                        joinWord = joinWord + " ";
                    joinWord = joinWord + subWords.get(k);
                }
                if (wordAppearances.containsKey(joinWord))
                    for (var type : wordAppearances.get(joinWord).keySet())
                    {
                        var segWord = new SegmentWord(joinWord, type, i, j);
                        vs.add(segWord);
                    }
            }
        var g = Graph.relationGraph(vs,
                (x, y) -> y.Start - x.End == 1
        );

        var errorWord = Utilities.firstCase(Utilities.range(0, words.size() - 1),
                i -> !Utilities.anyTrue(g.vertexList(), x -> x.Start <= i && i <= x.End), (Integer) null
        );
        if (errorWord != null)
            throw new RuntimeException("Unable to process at the word '" + words.get(errorWord) + "'");
        var nextTypes = getNextTypes();
        var beforeTypes = getBeforeTypes();
        for (var ed : ((Graph<SegmentWord>) (Object) g).edgeList())
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            var lS = NullFunction.createInstance(() ->
            {
                return getNextBeforeLeastSquare();
            }).apply();
            var nextWeight = NullFunction.createInstance(() ->
            {
                if (Utilities.keySequenceExistsQ(nextTypes, v0.Word, v0.Type))
                {
                    var corres = nextTypes.get(v0.Word).get(v0.Type);
                    var sum = Utilities.sum(
                            x -> isSimilarType(x, v1.Type) ? corres.get(x) : 0,
                            corres.keySet());
                    return sum;
                } else return 0d;
            }).apply();
            var beforeWeight = NullFunction.createInstance(() ->
            {
                if (Utilities.keySequenceExistsQ(beforeTypes, v1.Word, v1.Type))
                {
                    var corres = beforeTypes.get(v1.Word).get(v1.Type);
                    var sum = Utilities.sum(
                            x -> isSimilarType(x, v0.Type) ? corres.get(x) : 0,
                            corres.keySet());
                    return sum;
                } else return 0d;
            }).apply();
            var prods = Utilities.mapThread(
                    (x, y) -> x.doubleValue() * y.doubleValue(),
                    (ArrayList<Number>) (Object) lS,
                    (ArrayList<Number>) Utilities.toArrayList(new Number[]{
                            wordAppearances.get(v0.Word).get(v0.Type),
                            wordAppearances.get(v1.Word).get(v1.Type), nextWeight, beforeWeight
                    })
            );
            g.setEdgeWeight(ed, Utilities.sum(prods));
        }
        BinaryFunction<SegmentWord, SegmentWord, Boolean> isSubword = (word0, word1) -> word1.Start <= word0.Start && word0.End <= word1.End;
        for (var ed : g.edgeList())
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            if (Utilities.anyTrue(g.vertexList(), x -> isSubword.apply(v0, x) && isSubword.apply(v1, x)))
            {
                var auxVs = Utilities.select(g.edgeList(),
                        x -> x.contains(v0) || x.contains(v1)
                );
                Utilities.map(x ->
                {
                    g.setEdgeWeight(x, -1d);
                }, auxVs);
            }
        }
        var edgeWeightf = new HashMap<ArrayList<SegmentWord>, Double>();
        Utilities.map(x ->
        {
            edgeWeightf.put(x, -g.getEdgeWeight(x));
        }, g.edgeList());
        var firstVs = Utilities.select(g.vertexList(),
                x -> x.Start == 0
        );
        var lastVs = Utilities.select(g.vertexList(),
                x -> x.End == words.size() - 1
        );
        var h = (Graph<Object>) (Object) g.clone();
        var objEdgeWeightf = (HashMap<ArrayList<Object>, Double>) (Object) edgeWeightf;
        final var source = "s";
        final var target = "t";
        h.addVertex(source);
        h.addVertex(target);
        for (var v : firstVs)
        {
            h.addEdge(source, v);
            h.setEdgeWeight(source, v, 0d);
            var aux = new CustomArrayList<>(new Object[]{source, v});
            objEdgeWeightf.put(aux, 0d);
        }
        for (var v : lastVs)
        {
            h.addEdge(v, target);
            h.setEdgeWeight(v, target, 0d);
            var aux = new CustomArrayList<>(new Object[]{v, target});
            objEdgeWeightf.put(aux, 0d);
        }
        var stRes = h.shortestPath(source, target, objEdgeWeightf);
        if (stRes == null)
        {
            var outCompos = NullFunction.createInstance(() ->
            {
                var aux = h.vertexOutComponent(source);
                Utilities.deleteCases(aux,
                        x -> x instanceof String
                );
                return (Collection<SegmentWord>) (Object) aux;
            }).apply();
            var maxOutIndex = Utilities.max(Utilities.map(x -> x.End, outCompos));
            var inCompos = NullFunction.createInstance(() ->
            {
                var aux0 = h.vertexInComponent(target);
                Utilities.deleteCases(aux0, x -> x instanceof String);
                var aux1 = (Collection<SegmentWord>) (Object) aux0;
                var selectedVs = Utilities.select(aux1,
                        x -> x.Start > maxOutIndex
                );
                return selectedVs;
            }).apply();
            var minInIndex = Utilities.min(Utilities.map(x -> x.Start, inCompos));
            var errorWordRange = NullFunction.createInstance(() ->
            {
                var aux = Utilities.part(words, maxOutIndex + 1, minInIndex - 1);
                var auxRes = "";
                for (var i = 0; i <= aux.size() - 1; i++)
                {
                    if (i > 0)
                        auxRes += " ";
                    auxRes += aux.get(i);
                }
                return auxRes;
            });
            throw new RuntimeException("unable to process at '" + errorWordRange + "'");
        }
        UnaryFunction<ArrayList<SegmentWord>, Double> pathToWeight = (path) ->
        {
            var preRes = Utilities.table(i ->
            {
                var aux = new ArrayList<SegmentWord>();
                aux.add(path.get(i));
                aux.add(path.get(i + 1));
                return edgeWeightf.get(aux);
            }, 0, path.size() - 2);
            return Utilities.sum(preRes);
        };
        var res = (ArrayList<SegmentWord>) (Object) Utilities.part(stRes, 1, stRes.size() - 2);
        final var resWrapped = new AtomicReference<ArrayList<SegmentWord>>();
        resWrapped.set(res);
        while (true)
        {
            var metQ = false;
            var deletedVs = Utilities.select(h.vertexList(), x ->
            {
                if (x instanceof String)
                    return false;
                var originX = (SegmentWord) x;
                return Utilities.anyTrue(resWrapped.get(),
                        y ->
                        {
                            var check = originX.Start == y.Start && originX.End == y.End;
                            if (!check)
                                return false;
                            return wordAppearances.get(y.Word).get(y.Type) > wordAppearances.get(originX.Word).get(originX.Type);
                        }
                );
            });
//            if(deletedVs.size()==0)
//                break;
            h.deleteVertices(deletedVs);
            for (var v : res)
            {
                var copiedH = h.clone();
                copiedH.deleteVertex(v);
                var stPath = copiedH.shortestPath(source, target, objEdgeWeightf);
                if (stPath != null)
                {
                    var auxPath = (ArrayList<SegmentWord>) (Object) Utilities.part(stPath, 1, stPath.size() - 2);
                    if (pathToWeight.apply(auxPath) <= pathToWeight.apply(res))
                    {
                        res = auxPath;
                        resWrapped.set(res);
                        h.deleteVertex(v);
                        h.deleteEdges(h.edgeList());
                        h.addEdges(copiedH.edgeList());
                        Utilities.map(
                                ed ->
                                {
                                    h.setEdgeWeight(ed, copiedH.getEdgeWeight(ed));
                                }, h.edgeList());
                        metQ = true;
                        break;
                    }
                }
            }
            if (!metQ)
                break;
        }
        return res;
    }

    public static ArrayList<WordVertex> chooseTypes(ArrayList<String> sentence)
    {
        var wordAppearances = getWordAppearances();
        var vs = new HashSet<WordVertex>();
        for (var i = 0; i <= sentence.size() - 1; i++)
        {
            var iWord = sentence.get(i);
            var types = wordAppearances.get(iWord).keySet();
            for (var type : types)
            {
                var wordVertex = new WordVertex(i, iWord, type);
                vs.add(wordVertex);
            }
        }
        var g = Graph.relationGraph(vs,
                (x, y) -> y.Location - x.Location == 1
        );
        var nextTypes = getNextTypes();
        for (var ed : g.edgeList())
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            if (Utilities.keySequenceExistsQ(nextTypes, v0.Word, v0.Type))
                g.setEdgeWeight(ed,
                        Utilities.sum(x -> (isSimilarType(x, v1.Type) ? nextTypes.get(v0.Word).get(v0.Type).get(x) : 0),
                                nextTypes.get(v0.Word).get(v0.Type).keySet())
                );
            else g.setEdgeWeight(ed, 0);
        }
        var maxEdgeWeight = Utilities.maxBy(
                Utilities.map((ArrayList<WordVertex> x) -> g.getEdgeWeight(x),
                        g.edgeList()), y -> y
        );
        var edgeWeightf = new HashMap<ArrayList<WordVertex>, Double>();
        Utilities.map(
                ed ->
                {
                    edgeWeightf.put(ed, maxEdgeWeight - g.getEdgeWeight(ed));
                }, g.edgeList()
        );
        var firstVs = Utilities.select(g.vertexList(),
                x -> g.vertexInDegree(x) == 0
        );
        var lastVs = Utilities.select(g.vertexList(),
                x -> g.vertexOutDegree(x) == 0
        );
        var paths = new ArrayList<ArrayList<WordVertex>>();
        for (var v0 : firstVs)
            for (var v1 : lastVs)
            {
                var path = g.shortestPath(v0, v1, edgeWeightf);
                if (path != null)
                    paths.add(path);
            }
        var res = Utilities.minBy(paths,
                path ->
                {
                    var eds = Utilities.table(
                            (i) ->
                            {
                                var ed = new ArrayList<WordVertex>();
                                ed.add(path.get(i));
                                ed.add(path.get(i + 1));
                                return edgeWeightf.get(ed);
                            }
                            , 0, path.size() - 2);
                    return Utilities.sum(eds);
                }
        );
        return res;
    }

    public static HashMap<String, HashMap<String, HashMap<String, Integer>>> BeforeTypes = null;

    public static HashMap<String, HashMap<String, HashMap<String, Integer>>> getBeforeTypes()
    {
        if (BeforeTypes != null)
            return BeforeTypes;
        BeforeTypes = getConnectingTypes("before");
        return BeforeTypes;
    }

    public static HashMap<String, HashMap<String, HashMap<String, Integer>>> NextTypes = null;

    public static HashMap<String, HashMap<String, HashMap<String, Integer>>> getNextTypes()
    {
        if (NextTypes != null)
            return NextTypes;
        NextTypes = getConnectingTypes("next");
        return NextTypes;
    }

    public static HashMap<String, HashMap<String, HashMap<String, Integer>>> getConnectingTypes(String direction)
    {
        var res = new HashMap<String, HashMap<String, HashMap<String, Integer>>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            var vs = Utilities.makeArrayList(tree.vertexList());
            Utilities.sortBy(vs, x -> x.Location);
            for (var i = 0; i <= vs.size() - 2; i++)
            {
                var iV = vs.get(i);
                var nextIV = vs.get(i + 1);
                if (nextIV.Location - iV.Location == 1)
                {
                    switch (direction)
                    {
                        case "next":
                            Utilities.insertValue(res,
                                    new Object[]{iV.Word, iV.Type, nextIV.Type},
                                    0, x -> x + 1
                            );
                            break;
                        case "before":
                            Utilities.insertValue(res,
                                    new Object[]{nextIV.Word, nextIV.Type, iV.Type},
                                    0, x -> x + 1
                            );
                            break;
                        default:
                            throw new RuntimeException("direction error");
                    }
                }
            }
//            for (var v : vs)
//            {
//                var nextV = Utilities.firstCase(vs,
//                        x -> x.Location - v.Location == 1, (WordVertex) null
//                );
//                if (nextV != null)
//                    Utilities.insertValue(res,
//                            new Object[]{v.Word, v.Type, nextV.Type},
//                            0, x -> x + 1
//                    );
//            }
        }
        return res;
    }

    public static boolean isPronounAdverbPropertyError(Graph<WordVertex> tree, WordVertex v)
    {
        if (!v.Type.equals("P"))
            return false;
        var pAds = getPronounAdverbProperties();
        if (!pAds.containsKey(v.Word))
            return false;
        var property = pAds.get(v.Word);
        if (property.equals("adverb"))
        {
            if (!isPLikeAdverb(tree, v))
                return true;
            else return false;
        } else return false /*if (isPLikeAdverb(tree, v))
            return true;
        else return false*/;
    }

    public static boolean isPLikeAdverb(Graph<WordVertex> tree, WordVertex v)
    {
        if (!v.Type.equals("P"))
            return false;
        if (tree.vertexInDegree(v) != 0)
            return false;
        var ed = Utilities.firstCase(tree.edgeList(), x -> x.get(0).equals(v),
                (ArrayList<WordVertex>) null);
        if (ed == null)
            return false;
        var dir = getEdgeDirection(ed);
        if (!dir.equals("before"))
            return false;
        var v1 = ed.get(1);
        return (v1.Type.equals("P") || v1.Type.startsWith("N")) && NullFunction.createInstance(() ->
        {
            var betweens = Utilities.select(tree.vertexList(),
                    x -> v1.Location < x.Location && x.Location < v.Location
            );
            return Utilities.allTrue(betweens,
                    x -> x.Type.startsWith("N") || Utilities.memberQ(new String[]{"P", "A"}, x.Type)
            );
        }).apply();
    }

    public static HashMap<String, String> PronounAdverbProperties = null;

    public static HashMap<String, String> getPronounAdverbProperties()
    {
        if (PronounAdverbProperties != null)
            return PronounAdverbProperties;
        var counter = new HashMap<String, HashMap<String, Integer>>();
        final var advStr = "adverb";
        final var nonAdvStr = "nonAdverb";
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                if (v.Type.equals("P"))
                {
                    if (isPLikeAdverb(tree, v))
                        Utilities.insertValue(counter,
                                new Object[]{v.Word, advStr}, 0, x -> x + 1
                        );
                    else
                        Utilities.insertValue(counter,
                                new Object[]{v.Word, nonAdvStr}, 0, x -> x + 1
                        );
                }
            }
        }
        var sums = Utilities.map(key ->
        {
            var corres = counter.get(key);
            return Utilities.sum(corres.values());
        }, counter.keySet());
        var sumMean = Utilities.mean(sums);
        Utilities.removeKeys(counter,
                key ->
                {
                    var corres = counter.get(key);
                    var sum = Utilities.sum(corres.values());
                    return sum < sumMean;
                }
        );
        var pairs = Utilities.map(key ->
        {
            var corres = counter.get(key);
            var values = Utilities.makeArrayList(corres.values());
            if (values.size() == 1)
                values.add(0);
            Utilities.sortBy(values, x -> x);
            return values;
        }, counter.keySet());
        var lS = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) pairs).get(0);
        var res = new HashMap<String, String>();
        for (var P : counter.keySet())
        {
            var corres = counter.get(P);
            var advValue = corres.containsKey(advStr) ? corres.get(advStr) : 0;
            var nonAdvValue = corres.containsKey(nonAdvStr) ? corres.get(nonAdvStr) : 0;
            if (advValue > lS * nonAdvValue)
                res.put(P, advStr);
            else if (nonAdvValue > lS * advValue)
                res.put(P, nonAdvStr);
        }
        PronounAdverbProperties = res;
        return res;
    }

    public static ArrayList<String> getClosestToRootPattern(Graph<WordVertex> tree)
    {
        var root = getRoot(tree);
        var inVs = Utilities.select(tree.inGoingVertices(root),
                x -> x.Location < root.Location
        );
        if (inVs.size() == 0)
            return null;
        Utilities.sortBy(inVs, x -> x.Location);
        var lastV = Utilities.getLastElement(inVs);
        var subTree = tree.subgraph(tree.vertexInComponent(lastV));
        return getFromLastTypePattern(subTree);
    }

    public static HashMap<Integer, HashMap<ArrayList<String>, Integer>> RootLocalStructures = null;

    public static HashMap<Integer, HashMap<ArrayList<String>, Integer>> getRootLocalStructures()
    {
        if (RootLocalStructures != null)
            return RootLocalStructures;
        var res = new HashMap<Integer, HashMap<ArrayList<String>, Integer>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            if (!isSpanningTree(tree))
                continue;
            var root = getRoot(tree);
            if (!root.Type.equals("V"))
                continue;
            tree.deleteVertices(x -> isAdverb(tree, x));
            var pattern = getClosestToRootPattern(tree);
            if (pattern == null)
                continue;
            for (var i = 1; i <= pattern.size() - 1; i++)
            {
                if (i + 1 > 4)
                    break;
                var subPattern = Utilities.part(pattern, 0, i);
                Utilities.insertValue(res,
                        new Object[]{i + 1, subPattern}, 0, x -> x + 1
                );
            }
        }
        for (var length : res.keySet())
        {
            var corres = res.get(length);
            var mean = Utilities.mean(corres.values());
            Utilities.removeKeys(corres,
                    x -> corres.get(x) < mean
            );
        }
        RootLocalStructures = res;
        return res;
    }

    public static ArrayList<String> getFromLastTypePattern(Graph<WordVertex> tree)
    {
        var res = new ArrayList<String>();
        if (tree.vertexCount() == 0)
            return res;
        if (tree.vertexCount() == 1)
        {
            res.add(Utilities.getFirstElement(tree.vertexList()).Type);
            return res;
        }
        var copiedTree = tree.clone();
        var root = getRoot(copiedTree);
        copiedTree.deleteEdges(ed -> ed.get(1).equals(root));
        var newRoots = Utilities.makeArrayList(
                Utilities.select(copiedTree.vertexList(), x -> copiedTree.vertexOutDegree(x) == 0)
        );
        Utilities.sortBy(newRoots, x -> -x.Location);
        for (var i = 0; i <= newRoots.size() - 1; i++)
        {
            var iV = newRoots.get(i);
            var inCompos = copiedTree.vertexInComponent(iV);
            var subG = copiedTree.subgraph(inCompos);
            var subRes = getFromLastTypePattern(subG);
            res.addAll(subRes);
        }
        return res;
    }

    public static boolean isTernaryLocalError(Graph<WordVertex> tree, WordVertex v)
    {
        var ternaryLocs = getTernaryLocals();
        var inVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                x -> !isAdverb(tree, x))
        );
        Utilities.sortBy(inVs, x -> x.Location);
        if (inVs.size() >= 2)
            for (var i = 0; i <= inVs.size() - 2; i++)
            {
                var iEle = inVs.get(i);
                var nextIEle = inVs.get(i + 1);
                var ar = new WordVertex[]{v, iEle, nextIEle};
                var locs = simplifyIndices(Utilities.map(x -> x.Location, ar));
                var types = Utilities.map(x -> x.Type, ar);
//                if (ternaryLocs.containsKey(locs))
//                    if (!ternaryLocs.get(locs).containsKey(types))
//                        return true;
                return !(ternaryLocs.containsKey(locs) && ternaryLocs.get(locs).containsKey(types));
            }
        else if (inVs.size() == 1)
        {
            var ele = inVs.get(0);
            var ar = new WordVertex[]{v, ele};
            var locs = simplifyIndices(Utilities.map(x -> x.Location, ar));
            var types = Utilities.map(x -> x.Type, ar);
//            if (ternaryLocs.containsKey(locs))
//                if (!ternaryLocs.get(locs).containsKey(types))
//                    return true;
            return !(ternaryLocs.containsKey(locs) && ternaryLocs.get(locs).containsKey(types));
        }
        return false;
    }

    public static HashMap<ArrayList<Integer>, HashMap<ArrayList<String>, Integer>> TernaryLocals = null;

    public static HashMap<ArrayList<Integer>, HashMap<ArrayList<String>, Integer>> getTernaryLocals()
    {
        if (TernaryLocals != null)
            return TernaryLocals;
        var counter = new HashMap<ArrayList<Integer>, HashMap<ArrayList<String>, Integer>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            tree.deleteVertices(x -> isAdverb(tree, x));
            for (var v : tree.vertexList())
            {
                var inVs = Utilities.makeArrayList(tree.inGoingVertices(v));
                Utilities.sortBy(inVs, x -> x.Location);
                if (inVs.size() >= 2)
                    for (var i = 0; i <= inVs.size() - 2; i++)
                    {
                        var iEle = inVs.get(i);
                        var nextIEle = inVs.get(i + 1);
                        var ar = new WordVertex[]{v, iEle, nextIEle};
                        var indices = Utilities.map(x -> x.Location, ar);
                        indices = simplifyIndices(indices);
                        var typeTuple = Utilities.map(x -> x.Type, ar);
                        Utilities.insertValue(counter,
                                new Object[]{indices, typeTuple}, 0, x -> x + 1
                        );
                    }
                else if (inVs.size() == 1)
                {
                    var ele = inVs.get(0);
                    var ar = new WordVertex[]{v, ele};
                    var indices = Utilities.map(x -> x.Location, ar);
                    indices = simplifyIndices(indices);
                    var typeTuple = Utilities.map(x -> x.Type, ar);
                    Utilities.insertValue(counter,
                            new Object[]{indices, typeTuple}, 0, x -> x + 1
                    );
                }
            }
        }
        var mean = Utilities.mean((Collection<Number>) (Object) getLeafValues(counter));
        var res = new HashMap<ArrayList<Integer>, HashMap<ArrayList<String>, Integer>>();
        for (var indices : counter.keySet())
            for (var typeTuple : counter.get(indices).keySet())
            {
                var value = counter.get(indices).get(typeTuple);
                if (value >= mean)
                    Utilities.insertValue(res,
                            new Object[]{indices, typeTuple}, value
                    );
            }
        TernaryLocals = res;
        return res;
    }

    public static boolean isCloseSeparationError(Graph<WordVertex> tree, WordVertex v)
    {
        var nextVs = findClosestWordVertices(tree, v);
        for (var nextV : nextVs)
        {
            var typePair = new CustomArrayList<>(new String[]{v.Type, nextV.Type});
            var cS = getCloseSeparation();
            if (cS.containsKey(typePair))
            {
                var state = cS.get(typePair);
                if (state.equals("closed"))
                {
                    {
                        var closeMean = CloseCounter.get(typePair);
                        var edWeight = getEdgeWeight(v, nextV);
                        if (edWeight >= closeMean)
                            if (!Utilities.anyTrue(tree.edgeList(), ed -> ed.contains(v) && ed.contains(nextV)))
                                return true;
                    }
                } else if (Utilities.anyTrue(tree.edgeList(), ed -> ed.contains(v) && ed.contains(nextV)))
                    return true;
            }
        }
        return false;
    }

    public static HashMap<ArrayList<String>, String> CloseSeparation = null;

    public static HashSet<WordVertex> findClosestWordVertices(Graph<WordVertex> tree, WordVertex v)
    {
        var vs = Utilities.makeArrayList(tree.vertexList());
        Utilities.sortBy(vs, x -> x.Location);
        var res = new HashSet<WordVertex>();
        var vPos = Utilities.firstPosition(vs, x -> x.equals(v));
        if (vPos == null)
            return res;
        for (var i = vPos + 1; i <= vs.size() - 1; i++)
        {
            var iEle = vs.get(i);
            var beforeEle = vs.get(i - 1);
            if (iEle.Location - beforeEle.Location != 1)
                break;
            else
            {
                res.add(iEle);
                if (!isAdverb(tree, iEle))
                    break;
            }
        }
        return res;
    }

    public static HashMap<ArrayList<String>, Double> CloseCounter = null;

    public static HashMap<ArrayList<String>, String> getCloseSeparation()
    {
        if (CloseSeparation != null)
            return CloseSeparation;
        var counter = new HashMap<ArrayList<String>, HashMap<String, Integer>>();
        var closeCounter = new HashMap<ArrayList<String>, Double[]>();
        final var closedStr = "closed";
        final var separatedStr = "separated";
        final var closeCountStr = "closeCount";
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                var nextVs = findClosestWordVertices(tree, v);
                for (var nextV : nextVs)
                {
                    if (Utilities.anyTrue(tree.edgeList(), ed -> ed.contains(v) && ed.contains(nextV)))
                    {
                        Utilities.insertValue(counter, new Object[]{
                                new CustomArrayList<>(new String[]{v.Type, nextV.Type})
                                , closedStr}, 0, x -> x + 1);
                        Utilities.insertValue(closeCounter,
                                new Object[]{new CustomArrayList<>(new String[]{v.Type, nextV.Type})},
                                new Double[]{0d, 0d},
                                x ->
                                {
                                    x[0] += getEdgeWeight(v, nextV);
                                    x[1] += 1d;
                                    return x;
                                }
                        );
                    } else Utilities.insertValue(counter, new Object[]{
                            new CustomArrayList<>(new String[]{v.Type, nextV.Type})
                            , separatedStr}, 0, x -> x + 1);
                }
            }
        }
        var sums = Utilities.map(
                x ->
                {
                    var aux = counter.get(x).values();
                    return Utilities.sum(aux);
                }, counter.keySet()
        );
        var sumMean = Utilities.mean(sums);
        Utilities.removeKeys(counter, key -> Utilities.sum(counter.get(key).values()) < sumMean);
        var appPairs = new ArrayList<ArrayList<Integer>>();
        for (var typePair : counter.keySet())
        {
            var appPair = Utilities.makeArrayList(counter.get(typePair).values());
            if (appPair.size() == 1)
                appPair.add(0);
            Utilities.sortBy(appPair, x -> x);
            appPairs.add(appPair);
        }
        var lS = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) appPairs).get(0);
        var res = new HashMap<ArrayList<String>, String>();
        Utilities.map(key ->
                {
                    var clsp = counter.get(key);
                    var closedValue = clsp.containsKey(closedStr) ? clsp.get(closedStr) : 0;
                    var separatedValue = clsp.containsKey(separatedStr) ? clsp.get(separatedStr) : 0;
                    if (closedValue > separatedValue * lS)
                        Utilities.insertValue(res,
                                new Object[]{key}, closedStr
                        );
                    else if (closedValue * lS < separatedValue)
                        Utilities.insertValue(res,
                                new Object[]{key}, separatedStr
                        );
                }, counter.keySet()
        );
//        res.remove(new CustomArrayList<>(new String[]{"V", "E"}));
        Utilities.removeKeys(counter, x -> !res.containsKey(x));
        Utilities.removeKeys(closeCounter, x -> !res.containsKey(x));
        CloseCounter = new HashMap<>();
        Utilities.insertValues(CloseCounter, closeCounter, () -> 0d,
                (Double x, Double[] y) -> x + y[1].doubleValue() == 0d ? 1d : (y[0] / y[1])
        );
//        Utilities.executeMathematicaCode("MyObject=%0", counter);
        CloseSeparation = res;
        return res;
    }

    public static boolean isNounMeaningSupplementError(Graph<WordVertex> tree, WordVertex v)
    {
        UnaryFunction<WordVertex, Boolean> isNoun = (x) -> x.Type.startsWith("N") || x.Type.equals("P");
        if (!isNoun.apply(v))
            return false;
        return Utilities.anyTrue(tree.vertexList(), (WordVertex x) ->
        {
            var check0 = x.Location == v.Location + 1;
            if (!check0)
                return false;
            if (!isNoun.apply(x))
                return false;
            return !(Utilities.anyTrue(tree.edgeList(),
                    ed -> ed.contains(x) && ed.contains(v)) || Utilities.anyTrue(tree.vertexList(),
                    y -> isNoun.apply(y) && y.Location < v.Location && tree.containsEdge(v, y)
                            && tree.containsEdge(x, y))
            );
        });
    }

    public static boolean isAdjectiveToVerbError(Graph<WordVertex> tree, WordVertex v)
    {
        var check0 = v.Type.equals("A");
        if (!check0)
            return false;
        var check1 = tree.vertexOutDegree(v) != 0;
        if (!check1)
            return false;
        var ed = Utilities.firstCase(tree.edgeList(), y -> y.get(0).equals(v));
        var v1 = ed.get(1);
        if (!v1.Type.equals("V"))
            return false;
        var inVs = tree.inGoingVertices(v1);
        if (v.Location < v1.Location)
            return Utilities.anyTrue(inVs, x -> x.Location < v.Location);
        else return Utilities.anyTrue(inVs, x -> x.Location > v.Location);
    }

    public static HashSet<ArrayList<String>> EndingErrorPs = null;

    public static HashSet<ArrayList<String>> getEndingErrorPs()
    {
        if (EndingErrorPs != null)
            return EndingErrorPs;
        var counter = new HashMap<ArrayList<String>, Integer>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
                if (isTypeEndingError(tree, v, x -> x.Type.equals("P")))
                    Utilities.insertValue(counter,
                            new Object[]{
                                    new CustomArrayList<String>(new String[]{v.Word, v.Type})
                            }, 0, y -> y + 1
                    );
        }
        var selectedPairs = Utilities.select(counter.keySet(),
                x -> WordAppearances.get(x.get(0)).get(x.get(1)) >= getWordAppearanceMean()
        );
        var res = new HashMap<ArrayList<String>, Double>();
        Utilities.map(x ->
        {
            res.put(x, ((double) counter.get(x)) / WordAppearances.get(x.get(0)).get(x.get(1)));
        }, selectedPairs);
        var mean = Utilities.mean(res.values());
        EndingErrorPs = Utilities.makeHashSet(Utilities.select(res.keySet(),
                x -> res.get(x) < mean
        ));
        return EndingErrorPs;
    }

    public static boolean isClosestToRootEndingError(Graph<WordVertex> tree, WordVertex v)
    {
        if (!v.Type.equals("V") || tree.vertexOutDegree(v) != 0)
            return false;
        var copiedTree = tree.clone();
        copiedTree.deleteVertices(x -> isAdverb(copiedTree, x));
        var localStructures = getRootLocalStructures();
        var pattern = getClosestToRootPattern(copiedTree);
        if (pattern == null)
            return false;
        pattern = Utilities.part(pattern, 0, Math.min(3, pattern.size() - 1));
        for (var i = 1; i <= 3; i++)
        {
            if (i > pattern.size() - 1)
                break;
            var subPattern = Utilities.part(pattern, 0, i);
            if (!localStructures.get(i + 1).containsKey(subPattern))
                return true;
        }
        return false;
    }
//    public static boolean isNounEndingError(Graph<WordVertex> tree, WordVertex v)
//    {
//        var endingErrorPs = getEndingErrorPs();
//        return isTypeEndingError(tree, v, (x) -> x.Type.startsWith("N") || endingErrorPs.contains(
//                        new CustomArrayList<>(new String[]{x.Word, x.Type})
//                )
//        );
//    }

    public static boolean isTypeEndingError(Graph<WordVertex> tree, WordVertex v, UnaryFunction<WordVertex, Boolean> wordVertexCheck)
    {
        if (!isSpanningTree(tree))
            return false;
        if (!wordVertexCheck.apply(v))
            return false;
        BinaryFunction<ArrayList, ArrayList, ArrayList> commonPrefix = (x, y) ->
        {
            var res = new ArrayList<>();
            var min = Utilities.min(x.size(), y.size());
            for (var i = 0; i <= min - 1; i++)
                if (x.get(i).equals(y.get(i)))
                    res.add(x);
                else break;
            return res;
        };
        var coords = assignTreeCoordinate(tree);
        var root = getRoot(tree);
        if (!root.Type.equals("V"))
            return false;
        return NullFunction.createInstance(() ->
        {
            if (!v.equals(root) && (v.Location < root.Location))
            {
                var path = tree.findPath(v, root);
                if (path.size() > 2)
//                    if (!Utilities.anyTrue(path, x -> x.Type.equals("E")))
                    if (!Utilities.anyTrue(tree.vertexList(),
                            (WordVertex x) ->
                            {
                                var vCoord = coords.get(v);
                                var xCoord = coords.get(x);
                                return v.Location < x.Location && x.Location < root.Location &&
                                        commonPrefix.apply(vCoord, xCoord).size() >= 1 && !isAdverb(tree, x);
                            }
                    ))
                        return true;
            }
            return false;
        }).apply() && NullFunction.createInstance(() ->
        {
            var path = tree.findPath(v, root);
            var secondLastV = path.get(path.size() - 2);
            var inVs = tree.vertexInComponent(secondLastV);
            var subG = tree.subgraph(inVs);
            var insideVs = Utilities.select(subG.vertexList(),
                    x ->
                    {
                        if (subG.vertexOutDegree(x) == 0)
                            return false;
                        var ed = Utilities.firstCase(subG.edgeList(),
                                y -> y.get(0).equals(x)
                        );
                        var x1 = ed.get(1);
                        var inx1s = subG.inGoingVertices(x1);
                        return Utilities.anyTrue(inx1s,
                                y -> y.Location > x.Location
                        );
                    }
            );
            return !(Utilities.allTrue(subG.vertexList(), x -> x.Type.equals("V") ||
                    x.Type.startsWith("N") || x.Type.equals("P") || x.Type.equals("E") || isAdverb(subG, x)) &&
                    Utilities.allTrue(insideVs, x -> isAdverb(subG, x) || x.Type.startsWith("N"))
            );
        }).apply();
    }

    public static Double WordOutcomingAppearanceMean = null;

    public static Double getWordOutcomingAppearanceMean()
    {
        if (WordOutcomingAppearanceMean != null)
            return WordOutcomingAppearanceMean;
        WordOutcomingAppearanceMean = getWordConnectingAppearanceMean("outcoming");
        return WordOutcomingAppearanceMean;
    }

    public static Double WordIncomingAppearanceMean = null;

    public static double getWordIncomingAppearanceMean()
    {
        if (WordIncomingAppearanceMean != null)
            return WordIncomingAppearanceMean;
        WordIncomingAppearanceMean = getWordConnectingAppearanceMean("incoming");
        return WordIncomingAppearanceMean;
    }

    public static double getWordConnectingAppearanceMean(String loc)
    {
        var wordConnectingTypes = (HashMap<String, HashMap<String, HashMap<String, HashMap<String, Integer>>>>) (loc.equals("incoming") ? getWordIncomingTypes() : getWordOutcomingTypes());
        var values = new ArrayList<Integer>();
        for (var word : wordConnectingTypes.keySet())
            for (var type : wordConnectingTypes.get(word).keySet())
                for (var dir : wordConnectingTypes.get(word).get(type).keySet())
                    if (!dir.equals("undefined"))
                        for (var type1 : wordConnectingTypes.get(word).get(type).get(dir).keySet())
                            values.add(wordConnectingTypes.get(word).get(type).get(dir).get(type1));
        return Utilities.mean(values);
    }

    public static int typePerfectConnectingTypesErrorCompare(Graph<WordVertex> tree0, Graph<WordVertex> tree1)
    {
        return typePerfectConnectingTypesErrorCompare(tree0, tree1, false);
    }

    public static int typePerfectConnectingTypesErrorCompare(Graph<WordVertex> tree0, Graph<WordVertex> tree1, boolean showDiff)
    {
        var globalError = getTypePerfectConnectingTypesError();
        var followingSum = Utilities.sum((Collection<Integer>) (Object) getLeafValues(globalError.get("following")));
        var precedingSum = Utilities.sum((Collection<Integer>) (Object) getLeafValues(globalError.get("preceding")));
        var errors0 = getTypePerfectConnectingTypesError(tree0);
        var errors1 = getTypePerfectConnectingTypesError(tree1);
        var errorPairs0 = new ArrayList<ArrayList<Object>>();
        var errorPairs1 = new ArrayList<ArrayList<Object>>();
        for (var dir : globalError.keySet())
        {
            for (var type : globalError.get(dir).keySet())
                for (var tuple : globalError.get(dir).get(type).keySet())
                {
                    errorPairs0.add(
                            new CustomArrayList<Object>(new Object[]{
                                    new CustomArrayList<>(new Object[]{dir, type, tuple}),
                                    Utilities.keySequenceExistsQ(errors0, dir, type, tuple) ? errors0.get(dir).get(type).get(tuple) : 0,
                                    dir.equals("following") ? (int) followingSum : (int) precedingSum,
                                    globalError.get(dir).get(type).get(tuple)
                            })
                    );
                    errorPairs1.add(
                            new CustomArrayList<Object>(new Object[]{
                                    new CustomArrayList<>(new Object[]{dir, type, tuple}),
                                    Utilities.keySequenceExistsQ(errors1, dir, type, tuple) ? errors1.get(dir).get(type).get(tuple) : 0,
                                    dir.equals("following") ? (int) followingSum : (int) precedingSum,
                                    globalError.get(dir).get(type).get(tuple)
                            })
                    );
                }
        }
        var m = 2;
        var n = 3;
        Utilities.topologicalSort(errorPairs0,
                (x, y) -> Utilities.lexicographicOrder(
                        (ArrayList<Integer>) (Object) Utilities.part(x, m, n),
                        (ArrayList<Integer>) (Object) Utilities.part(y, m, n),
                        (u, v) -> u - v)
        );
        Utilities.topologicalSort(errorPairs1,
                (x, y) -> Utilities.lexicographicOrder(
                        (ArrayList<Integer>) (Object) Utilities.part(x, m, n),
                        (ArrayList<Integer>) (Object) Utilities.part(y, m, n),
                        (u, v) -> u - v)
        );
        var res = Utilities.lexicographicOrder(
                errorPairs0, errorPairs1,
                (x, y) -> ((int) x.get(1)) - ((int) y.get(1))
        );
        if (showDiff)
            if (res == 0)
                Utilities.executeMathematicaCode("Echo@\"Two trees are equal\"");
            else
            {
                for (var i = 0; i <= errorPairs0.size() - 1; i++)
                    if ((int) errorPairs0.get(i).get(1) != ((int) errorPairs1.get(i).get(1)))
                    {
                        Utilities.executeMathematicaCode("Echo[%0@toString[]];Echo[%1@toString[]];Echo[%2@toString[]];Echo[%3@toString[]]",
                                errorPairs0.get(i).get(0), errorPairs0.get(i).get(1),
                                errorPairs1.get(i).get(0), errorPairs1.get(i).get(1)
                        );
                        break;
                    }
            }
        return res;
    }

    public static HashMap<String, HashMap<String, HashMap<ArrayList<String>, Integer>>> TypePerfectConnectingTypesError = null;

    public static HashMap<String, HashMap<String, HashMap<ArrayList<String>, Integer>>> getTypePerfectConnectingTypesError()
    {
        if (TypePerfectConnectingTypesError != null)
            return TypePerfectConnectingTypesError;
        HashMap<String, HashMap<String, HashMap<ArrayList<String>, Integer>>> res = new HashMap<>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            var treeError = (HashMap<String, HashMap<String, HashMap<ArrayList<String>, Integer>>>) getTypePerfectConnectingTypesError(tree);
            Utilities.insertValues(res, treeError,
                    () -> 0,
                    (x, y) -> x + ((int) y)
            );
        }
        TypePerfectConnectingTypesError = res;
        return TypePerfectConnectingTypesError;
    }

    public static HashMap<String, HashMap<String, HashMap<ArrayList<String>, Integer>>> getTypePerfectConnectingTypesError(Graph<WordVertex> tree)
    {
        HashMap<String, HashMap<String, HashMap<ArrayList<String>, Integer>>> res = new HashMap<>();
        Utilities.insertValue(res,
                new Object[]{"following"},
                getTypePerfectConnectingTypesError(tree, "following")
        );
        Utilities.insertValue(res,
                new Object[]{"preceding"},
                getTypePerfectConnectingTypesError(tree, "preceding")
        );
        return res;
    }

    public static HashMap<String, HashMap<ArrayList<String>, Integer>> getTypePerfectConnectingTypesError(Graph<WordVertex> tree, String loc)
    {
        HashMap<String, HashMap<ArrayList<String>, Integer>> res = new HashMap<>();
        var typePerfectConnectingTypes = loc.equals("preceding") ? getTypePerfectPrecedingTypes() :
                getTypePerfectFollowingTypes();
        for (var v : tree.vertexList())
        {
            var selectedVs = Utilities.select(tree.inGoingVertices(v),
                    x -> (loc.equals("preceding") ? x.Location < v.Location : x.Location > v.Location) && !isAdverb(tree, x)
            );
            Utilities.sortBy(selectedVs, x -> x.Location);
            var types = Utilities.map(x -> x.Type, selectedVs);
            if (typePerfectConnectingTypes.containsKey(v.Type))
                for (var tuple : typePerfectConnectingTypes.get(v.Type))
                {
                    if (!tuple.equals(types))
                        Utilities.insertValue(res,
                                new Object[]{v.Type, tuple}, 0, x -> x + 1
                        );
                    else Utilities.insertValue(res,
                            new Object[]{v.Type, tuple}, 0, x -> x
                    );
                }
        }
        return res;
    }

    public static Graph<WordVertex> findABetterType(Graph<WordVertex> baseG,
                                                    Parser inputTree)
    {
        var wordApps = getWordAppearances();
        var tree = inputTree.clone();
        var hasBetterTree = false;
        var parserContainer = new AtomicReference<Parser>();
        parserContainer.set(null);
        while (true)
        {
            var metQ = false;
            var vs = tree.vertexList();
            var replacedVs = new ArrayList<WordVertex>();
            for (var v : vs)
            {
                var types = Utilities.makeHashSet(wordApps.get(v.Word).keySet());
                Utilities.deleteCases(types, x -> x.equals(v.Type));
                Utilities.map(
                        type ->
                        {
                            var auxV = new WordVertex(v.Location, v.Word, type);
                            replacedVs.add(auxV);
                        }, types);
            }
            Utilities.sortBy(replacedVs, x -> -wordApps.get(x.Word).get(x.Type));
            found:
            for (var otherV : replacedVs)
            {
                var v = Utilities.firstCase(vs, x -> x.Location == otherV.Location);
                final var map = new CustomHashMap<WordVertex, WordVertex>(new Object[][]{
                        {v, otherV}
                });
                parserContainer.set(tree);
                var otherTypeTree = NullFunction.createInstance(() ->
                {
                    var aux = parserContainer.get().clone();
                    var meaningEdges = aux.MeaningSupplementEdges;
                    meaningEdges = (HashSet<ArrayList<WordVertex>>) Utilities.replace(meaningEdges, map, 2);
                    var res = new Parser(Graph.vertexReplace(aux,
                            map
                    ));
                    res.MeaningSupplementEdges = meaningEdges;
                    return res;
                }).apply();
                if (otherTypeTree.vertexOutDegree(otherV) == 0 && errorTreeCompare(otherTypeTree, tree) < 0)
                {
                    var auxTree = decideParser(
                            Graph.vertexReplace(baseG, map)
                    );
                    if (errorTreeCompare(auxTree, tree) < 0)
                    {
                        tree = auxTree;
                        metQ = true;
                        hasBetterTree = true;
                        break;
                    }
                }
                var inVs = otherTypeTree.vertexInComponent(otherV);
                var outVs = Utilities.complement(otherTypeTree.vertexList(), inVs);
                for (var w : outVs)
                {
                    var auxOtherTypeTree = otherTypeTree.clone();
                    auxOtherTypeTree.deleteMeaningSupplementEdges();
                    var otherVCompos = Utilities.firstCase(
                            auxOtherTypeTree.weaklyConnectedComponents(),
                            x -> x.contains(otherV)
                    );
                    if (!otherVCompos.contains(w))
                        continue;
                    auxOtherTypeTree.deleteEdges(ed -> ed.get(0).equals(otherV));
                    auxOtherTypeTree.addEdge(otherV, w);
                    if (errorTreeCompare(auxOtherTypeTree, tree) < 0)
                    {
                        var auxTree = decideParser(
                                Graph.vertexReplace(baseG, map)
                        );
                        if (errorTreeCompare(auxTree, tree) < 0)
                        {
                            tree = auxTree;
                            metQ = true;
                            hasBetterTree = true;
                            break found;
                        }
                    }
                }
            }
            if (!metQ)
                break;
        }
        if (hasBetterTree)
            return tree;
        else return null;
    }

    public static Graph<WordVertex> oldfindABetterType(Graph<WordVertex> baseG, Graph<WordVertex> tree)
    {
        var baseGVs = baseG.vertexList();
        var appMean = getWordAppearanceMean();
        var error = countErrors(tree);
        var errorVs = Utilities.union((HashSet<WordVertex>) error.get(essentialOutsideStr),
                (HashSet<WordVertex>) error.get(essentialInsideStr)
        );
        var selectedVs = Utilities.select(Utilities.complement(baseGVs, tree.vertexList()),
                (x) -> Utilities.anyTrue(errorVs, y -> x.Location == y.Location)
        );
        Utilities.sortBy(selectedVs,
                x -> -WordAppearances.get(x.Word).get(x.Type)
        );
        for (var w : selectedVs)
        {
            var newTree = Graph.vertexReplace(tree,
                    Utilities.firstCase(tree.vertexList(), y -> y.Location == w.Location)
                    , w
            );
            newTree = findABetterParser(baseG.subgraph(newTree.vertexList()), newTree);
            if (errorTreeCompare(newTree, tree) < 0)
            {
                return newTree;
//                    var res = recursiveMaxTree(baseG.subgraph(newTree.vertexList()),
//                            new HashMap<>()
//                    );
//                    if (errorTreeCompare(res, tree) < 0)
//                        return res;
            }
        }
        return null;
    }

    public static HashSet<String> VocabularyTypes = null;

    public static HashSet<String> getVocabularyTypes()
    {
        if (VocabularyTypes != null)
            return VocabularyTypes;
        var res = new HashSet<String>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
                res.add(v.Type);
        }
        VocabularyTypes = res;
        return VocabularyTypes;
    }

    public static boolean isSimilarType(String type0, String type1)
    {
        if (type0.equals(type1))
            return true;
        if (type0.startsWith("N") && type1.startsWith("N"))
            return true;
        return false;
    }

    public static boolean isSimilarType(WordVertex v0, WordVertex v1)
    {
        var type0 = v0.Type;
        var type1 = v1.Type;
        return isSimilarType(type0, type1);
    }

    public static Graph<WordVertex> findABetterParser(Graph<WordVertex> baseG, Graph<WordVertex> tree)
    {
        var res = tree.clone();
        while (true)
        {
            var auxRes = preFindABetterParser(baseG, res);
            if (auxRes == null)
                return res;
            res = auxRes;
        }
    }

    public static Graph<WordVertex> preFindABetterParser(Graph<WordVertex> baseG, Graph<WordVertex> tree)
    {
        var vs = tree.vertexList();
        var root = Utilities.firstCase(vs, x -> tree.vertexOutDegree(x) == 0, (WordVertex) null);
        if (root == null)
            return null;
        var remainVs = getSortedErrorWordVertices(tree);
        remainVs = Utilities.join(remainVs, Utilities.complement(tree.vertexList(), remainVs));
        Utilities.deleteCases(remainVs, (x) -> x.equals(root));
        for (var i = 0; i <= remainVs.size() - 2; i++)
        {
            var iV = remainVs.get(i);
            var outiEd = Utilities.firstCase(tree.edgeList(), x -> x.get(0).equals(iV));
            var outiEds = Utilities.select(baseG.edgeList(),
                    x -> /*x.get(0).equals(iV)*/x.get(0).Location == iV.Location
            );
            for (var j = i + 1; j <= remainVs.size() - 1; j++)
            {
                var jV = remainVs.get(j);
                var outjEd = Utilities.firstCase(tree.edgeList(),
                        x -> /*x.get(0).equals(jV)*/x.get(0).Location == jV.Location
                );
                var outjEds = Utilities.select(baseG.edgeList(), x -> x.get(0).equals(jV));
                for (var ied : outiEds)
                    for (var jed : outjEds)
                    {
                        if (ied.equals(outiEd) && jed.equals(outjEd))
                            continue;
                        var copiedTree = new Graph<WordVertex>(tree.vertexList(), tree.edgeList());
                        copiedTree.deleteEdge(outiEd);
                        copiedTree.deleteEdge(outjEd);
                        copiedTree.addEdge(ied);
                        copiedTree.addEdge(jed);
                        if (isSpanningTree(copiedTree))
                        {
                            if (errorTreeCompare(copiedTree, tree) < 0)
                                return copiedTree;
                        }
                    }
            }
        }
        return null;
    }

    public static boolean isSpanningTree(Graph<WordVertex> g)
    {
        var vs = g.vertexList();
        if (Utilities.count(vs, x -> g.vertexOutDegree(x) == 0) != 1)
            return false;
        if (Utilities.anyTrue(vs, x ->
        {
            var deg = g.vertexOutDegree(x);
            return deg != 0 && deg != 1;
        })
        )
            return false;
        var root = Utilities.firstCase(vs, x -> g.vertexOutDegree(x) == 0);
        var inCompos = g.vertexInComponent(root);
        return inCompos.size() == vs.size();
    }

    public static boolean isStrictTopologicalFiner(Graph<WordVertex> tree0, Graph<WordVertex> tree1)
    {
        return isTopologicalFiner(tree0, tree1) && !isTopologicalFiner(tree1, tree0);
    }

    public static boolean isTopologicalFiner(Graph<WordVertex> tree0, Graph<WordVertex> tree1)
    {
        for (var v : tree0.vertexList())
        {
            var inVs0 = tree0.vertexInComponent(v);
            var inVs1 = tree1.vertexInComponent(v);
            if (!Utilities.containsAll(inVs1, inVs0))
                return false;
        }
        return true;
    }

    public static HashSet<String> AdverbPs = null;

    public static HashSet<String> getAdverbPs()
    {
        if (AdverbPs != null)
            return AdverbPs;
        var auxRes = new HashMap<String, HashMap<String, Integer>>();
        final var outsideStr = "outside";
        final var insideStr = "inside";
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                if (v.Type.equals("P"))
                {
                    var loc = tree.vertexInDegree(v) == 0 ? outsideStr : insideStr;
                    Utilities.insertValue(auxRes,
                            new Object[]{v.Word, loc}, 0, (x) -> x + 1
                    );
                }
            }
        }
        var res = Utilities.makeHashSet(Utilities.select(auxRes.keySet(),
                        (x) ->
                        {
                            var counter = auxRes.get(x);
                            return counter.containsKey(outsideStr) && !counter.containsKey(insideStr);
                        }
                )
        );
        AdverbPs = res;
        return AdverbPs;
    }

    public static boolean isAdverb(Graph<WordVertex> tree, WordVertex v)
    {
        var copied = tree.clone();
        var inVs = tree.vertexInComponent(v);
        inVs.remove(v);
        copied.deleteVertices(inVs);
        var check = preIsAdverb(copied, v);
        if (!check)
            return false;
        else
        {
            var auxInVs = tree.inGoingVertices(v);
            return Utilities.allTrue(auxInVs,
                    (x) -> preIsAdverb(tree, x)
            );
        }
    }

    public static boolean preIsAdverb(Graph<WordVertex> tree, WordVertex v)
    {
        if (v.Type.equals("R"))
            return true;
        if (tree.vertexInDegree(v) != 0)
            return false;
        else
        {
            var specs = new CustomHashSet<>(new String[]{"L", "M", "T", /*"C",*/ "X"});
            if (specs.contains(v.Type))
                return true;
        }
        if (tree.vertexOutDegree(v) != 0)
        {
            var outVEdge = Utilities.firstCase(tree.edgeList(), (x) -> x.get(0).equals(v));
            var pair = getEdgeTypePair(outVEdge);
            if (getEdgeDirection(outVEdge).equals("next"))
            {
                if (pair.equals(new CustomArrayList<>(new String[]{"A", "V"})))
                    return true;
            } else
            {
                var inVs = tree.inGoingVertices(outVEdge.get(1));
                if (Utilities.anyTrue(inVs, x -> x.Location > v.Location))
                    if (pair.equals(new CustomArrayList<>(new String[]{"A", "V"})))
                        return true;
            }
        }
        return false;
    }

    private static HashMap<String, Integer> ErrorPropertyImportance = null;

    public static HashMap<String, Integer> getErrorAppearanceStatics()
    {
        if (ErrorPropertyImportance != null)
            return ErrorPropertyImportance;
        var res = new HashMap<String, Integer>();
        for (var parser : Parsers)
        {
            var auxg = getDependenceGraph(parser);
            var errors = countErrors(auxg);
            for (var name : errors.keySet())
            {
                var origin = (Collection) errors.get(name);
                Utilities.insertValue(res,
                        new Object[]{name},
                        0, (x) -> x + origin.size()
                );
            }
        }
        ErrorPropertyImportance = res;
        return ErrorPropertyImportance;
    }

//    public static boolean isPerfectFollowingTypes(Graph<WordVertex> tree, ArrayList<WordVertex> ed)
//    {
//        var dir = getEdgeDirection(ed);
//        if (!dir.equals("before"))
//            return false;
//        var v1 = ed.get(1);
//        return isPerfectFollowingTypes(tree, v1);
//    }

    public static boolean isTypePerfectPrecedingTypesError(Graph<WordVertex> tree, WordVertex v)
    {
        var selectedVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                (x) -> x.Location < v.Location && !isAdverb(tree, x)
        ));
        Utilities.sortBy(selectedVs, (x) -> x.Location);
        var reducedMap = getReducedTypeMap();
        var precedTypes = Utilities.replaceAll(Utilities.map((x) -> x.Type, selectedVs), reducedMap);
        var pFTypes = new HashMap<String, HashSet<ArrayList<String>>>();
        var typePerfectPrecedingTypes = getTypePerfectPrecedingTypes();
        for (var type : typePerfectPrecedingTypes.keySet())
        {
            Utilities.insertValue(pFTypes,
                    new Object[]{reducedMap.get(type)},
                    new HashSet<ArrayList<String>>(),
                    x ->
                    {
                        var tuples = typePerfectPrecedingTypes.get(type);
                        for (var tuple : tuples)
                            x.add((ArrayList<String>) Utilities.replaceAll(tuple, reducedMap));
                        return x;
                    }
            );
        }
        var vType = reducedMap.get(v.Type);
        if (pFTypes.containsKey(vType))
            return !(pFTypes.containsKey(vType) && pFTypes.get(vType).contains(precedTypes));
        else return false;
    }

    public static boolean isTypePerfectFollowingTypesError(Graph<WordVertex> tree, WordVertex v)
    {
        if (!Utilities.memberQ(new String[]{"V", "E"}, v.Type))
            return false;
        var selectedVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                (x) -> x.Location > v.Location && !isAdverb(tree, x)
        ));
        Utilities.sortBy(selectedVs, (x) -> x.Location);
        var reducedMap = getReducedTypeMap();
        var folTypes = Utilities.replaceAll(Utilities.map((x) -> x.Type, selectedVs), reducedMap);
        var pFTypes = new HashMap<String, HashSet<ArrayList<String>>>();
        var typePerfectFollowingTypes = getTypePerfectFollowingTypes();
        for (var type : typePerfectFollowingTypes.keySet())
        {
            Utilities.insertValue(pFTypes,
                    new Object[]{reducedMap.get(type)},
                    new HashSet<ArrayList<String>>(),
                    x ->
                    {
                        var tuples = typePerfectFollowingTypes.get(type);
                        for (var tuple : tuples)
                            x.add((ArrayList<String>) Utilities.replaceAll(tuple, reducedMap));
                        return x;
                    }
            );
        }
        var vType = reducedMap.get(v.Type);
        if (pFTypes.containsKey(vType))
            return !(pFTypes.containsKey(vType) && pFTypes.get(vType).contains(folTypes));
        else return false;
    }

    public static HashMap<String, HashSet<ArrayList<String>>> getTypePerfectConnectingTypes(String loc, boolean withVariance)
    {
        var counter = new HashMap<String, HashMap<ArrayList<String>, Integer>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                var selectedVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                        (x) -> (loc.equals("following") ? x.Location > v.Location : x.Location < v.Location)
                                && !isAdverb(tree, x)
                ));
                Utilities.sortBy(selectedVs, (x) -> x.Location);
                var types = Utilities.map((x) -> x.Type, selectedVs);
                Utilities.insertValue(counter,
                        new Object[]{v.Type, types}, 0, (x) -> x + 1
                );
            }
        }
        var sums = new ArrayList<Integer>();
        for (var type : counter.keySet())
            sums.add((int) Utilities.sum(counter.get(type).values()));
        var sumMean = Utilities.mean(sums);
        var res = new HashMap<String, HashSet<ArrayList<String>>>();
        for (var type : counter.keySet())
        {
            var corres = counter.get(type);
            if (Utilities.sum(corres.values()) >= sumMean)
            {
                var values = corres.values();
                var valueMean = Utilities.mean(values);
                var variance = Utilities.variance(values);
                var selectedTuples = Utilities.makeHashSet(Utilities.select(corres.keySet(),
                        (x) -> corres.get(x) >= valueMean + (withVariance ? variance : 0)
                ));
                Utilities.insertValue(res,
                        new Object[]{type},
                        selectedTuples
                );
            }
        }
        return res;
    }

    public static HashMap<String, HashSet<ArrayList<String>>> TypePerfectPrecedingTypes = null;

    public static HashMap<String, HashSet<ArrayList<String>>> getTypePerfectPrecedingTypes()
    {
        if (TypePerfectPrecedingTypes != null)
            return TypePerfectPrecedingTypes;
        TypePerfectPrecedingTypes = getTypePerfectConnectingTypes("preceding", false);
        return TypePerfectPrecedingTypes;
    }

    public static HashMap<String, HashSet<ArrayList<String>>> TypePerfectFollowingTypes = null;

    public static HashMap<String, HashSet<ArrayList<String>>> getTypePerfectFollowingTypes()
    {
        if (TypePerfectFollowingTypes != null)
            return TypePerfectFollowingTypes;
        TypePerfectFollowingTypes = getTypePerfectConnectingTypes("following", false);
        return TypePerfectFollowingTypes;
    }

    private static HashMap<String, String> ReducedTypeMap = null;

    public static HashMap<String, String> getReducedTypeMap()
    {
        if (ReducedTypeMap != null)
            return ReducedTypeMap;
        var vocTypes = getVocabularyTypes();
        var similarTypesSet = Utilities.gatherBy(vocTypes, (x, y) -> isSimilarType(x, y));
        var res = new HashMap<String, String>();
        for (var similarTypes : similarTypesSet)
        {
            var firstEle = Utilities.getFirstElement(similarTypes);
            for (var type : similarTypes)
                res.put(type, firstEle);
        }
        ReducedTypeMap = res;
        return ReducedTypeMap;
    }

    public static boolean isTypePerfectAttaching(ArrayList<WordVertex> ed)
    {
        var pTA = getTypePerfectAttachings();
        var reducedTypeCorres = getReducedTypeMap();
        var reducedPTA = new HashMap<String, HashMap<String, HashSet<String>>>();
        for (var type0 : pTA.keySet())
            for (var dir : pTA.get(type0).keySet())
                for (var type1 : pTA.get(type0).get(dir))
                {
                    Utilities.insertValue(reducedPTA,
                            new Object[]{reducedTypeCorres.get(type0), dir},
                            new HashSet<String>(),
                            (x) ->
                            {
                                x.add(reducedTypeCorres.get(type1));
                                return x;
                            }
                    );
                }
        var reducedType0 = reducedTypeCorres.get(ed.get(0).Type);
        var reducedType1 = reducedTypeCorres.get(ed.get(1).Type);
        var dir = getEdgeDirection(ed);
        if (Utilities.keySequenceExistsQ(reducedPTA, new Object[]{reducedType0, dir}))
            return reducedPTA.get(reducedType0).get(dir).contains(reducedType1);
        else return true;
    }

    private static HashMap<String, HashMap<String, HashSet<String>>> TypePerfectAttachings = null;

    public static HashMap<String, HashMap<String, HashSet<String>>> getTypePerfectAttachings()
    {
        if (TypePerfectAttachings != null)
            return TypePerfectAttachings;
        var counter = new HashMap<>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            for (var ed : g.edgeList())
            {
                Utilities.insertValue(counter,
                        new Object[]{ed.get(0).Type, getEdgeDirection(ed), ed.get(1).Type},
                        0, (x) -> x + 1
                );
            }
        }
        var sums = new ArrayList<Integer>();
        for (var type : counter.keySet())
            for (var dir : new String[]{"next", "before"})
            {
                if (Utilities.keySequenceExistsQ(counter, type, dir))
                {
                    var corres = (HashMap<String, Integer>) Utilities.getValue(counter, type, dir);
                    sums.add((int) Utilities.sum(corres.values()));
                }
            }
        var sumMean = Utilities.mean(sums);
        HashMap<String, HashMap<String, HashSet<String>>> res = new HashMap<>();
        for (var type : counter.keySet())
            for (var dir : new String[]{"next", "before"})
            {
                if (Utilities.keySequenceExistsQ(counter, type, dir))
                {
                    var corres = (HashMap<String, Integer>) Utilities.getValue(counter, type, dir);
                    var values = corres.values();
                    var valueMean = Utilities.mean(values);
                    var sum = Utilities.sum(values);
                    if (sum >= sumMean)
                    {
                        var selectedTypes = Utilities.select(corres.keySet(),
                                (x) -> corres.get(x) >= valueMean
                        );
                        Utilities.insertValue(res, new Object[]{type, dir},
                                Utilities.makeHashSet(selectedTypes));
                    }
                }
            }
        /*Utilities.executeMathematicaCode("MyObject=%0",counter);*/
        TypePerfectAttachings = res;
        return TypePerfectAttachings;
    }

    public static boolean isMissingNoun(Graph<WordVertex> tree, WordVertex v)
    {
        var nounMissingVerbs = getNounMissingVerbs();
        if (!v.Type.equals("V") || tree.vertexOutDegree(v) == 0)
            return false;
        if (Utilities.anyTrue(tree.inGoingVertices(v), (x) -> x.Location < v.Location && (x.Type.startsWith("N") || x.Type.equals("P"))))
            return false;
        var ed = Utilities.firstCase(tree.edgeList(), (x) -> x.get(0).equals(v));
        var outV = ed.get(1);
        var direction = getEdgeDirection(ed);
        if (Utilities.keySequenceExistsQ(nounMissingVerbs, outV.Type, direction))
        {
            var avoids = (HashSet<String>) Utilities.getValue(nounMissingVerbs, outV.Type, direction);
            var selectedVs = Utilities.select(tree.vertexList(),
                    (x) ->
                    {
                        var tuple = new CustomArrayList<>(new Integer[]{v.Location, x.Location, outV.Location});
                        var check0 = Utilities.isOrdered(tuple, (y) -> y) || Utilities.isOrdered(
                                (ArrayList<Integer>) (Object) Utilities.reverse(tuple), (y) -> y
                        );
                        if (!check0)
                            return false;
                        var path0 = tree.findPath(tree, x, v);
                        var path1 = tree.findPath(tree, v, x);
                        return path0 == null && path1 == null;
                    }
            );
            return Utilities.anyTrue(selectedVs, (x) -> !avoids.contains(x));
        } else return false;
    }

    private static HashMap<String, HashMap<String, HashSet<String>>> NounMissingVerbs = null;

    public static HashMap<String, HashMap<String, HashSet<String>>> getNounMissingVerbs()
    {
        if (NounMissingVerbs != null)
            return NounMissingVerbs;
        var counter = new HashMap<>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                if (tree.vertexOutDegree(v) == 0 || !v.Type.equals("V"))
                    continue;
                var leftVs = Utilities.select(
                        Utilities.union(tree.inGoingVertices(v), tree.outGoingVertices(v)),
                        (x) -> x.Location < v.Location
                );
                if (!Utilities.anyTrue(leftVs, (x) -> x.Type.startsWith("N") || x.Type.equals("P")))
                {
                    var outV = Utilities.getFirstElement(tree.outGoingVertices(v));
                    var dir = v.Location < outV.Location ? "next" : "before";
                    var betweens = Utilities.select(tree.vertexList(),
                            (x) ->
                            {
                                var locs = (ArrayList<Integer>) Utilities.toArrayList(new Integer[]{v.Location, x.Location, outV.Location});
                                var check0 = Utilities.isOrdered(locs, (z, t) -> z - t);
                                var check1 = Utilities.isOrdered(
                                        (ArrayList<Integer>) (Object) Utilities.reverse(locs),
                                        (z, t) -> z - t
                                );
                                if (!check0 && !check1)
                                    return false;
                                return tree.findPath(x, v) == null && tree.findPath(v, x) == null;
                            }
                    );
                    for (var b : betweens)
                    {
                        Utilities.insertValue(counter,
                                new Object[]{outV.Type, dir, b.Type}, 0, (x) -> x + 1
                        );
                    }
                }
            }
        }
        var counterOrigin = (HashMap<String, HashMap<String, HashMap<String, Integer>>>) (Object) counter;
        var sums = new ArrayList<Integer>();
        for (var type : counterOrigin.keySet())
            for (var dir : new String[]{"next", "before"})
            {
                if (Utilities.keySequenceExistsQ(counterOrigin, type, dir))
                {
                    var values = counterOrigin.get(type).get(dir).values();
                    sums.add((int) Utilities.sum(values));
                }
            }
        var sumMean = Utilities.mean(sums);
        /*System.out.println(sumMean);*/
        var res = new HashMap<String, HashMap<String, HashSet<String>>>();
        for (var type : counterOrigin.keySet())
            for (var dir : new String[]{"next", "before"})
            {
                if (Utilities.keySequenceExistsQ(counterOrigin, type, dir))
                {
                    var statics = counterOrigin.get(type).get(dir);
                    var values = statics.values();
                    if (Utilities.sum(values) >= sumMean)
                    {
                        var mean = Utilities.mean(values);
                        var variance = Utilities.variance(values);
                        var selectedTypes = Utilities.makeHashSet(Utilities.select(statics.keySet(),
                                (x) -> statics.get(x) >= mean + variance
                        ));
                        Utilities.insertValue(res, new Object[]{type, dir}, selectedTypes);
                    }
                }
            }
        NounMissingVerbs = res;
        return NounMissingVerbs;
    }

    public static boolean isEWordPerfectFollowingTypes(Graph<WordVertex> tree, WordVertex v)
    {
        var pEF = getEWordPerfectFollowingTypes();
        if (!v.Type.equals("E"))
            return true;
        if (!pEF.containsKey(v.Word))
            return true;
        var inVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                        (x) -> x.Location > v.Location && !isAdverb(tree, x)
                )
        );
        Utilities.sortBy(inVs, (x) -> x.Location);
        var types = Utilities.map((x) -> x.Type, inVs);
        var reducedMap = getReducedTypeMap();
        var reducedTypeSet = (Set) Utilities.replaceAll(pEF.get(v.Word), reducedMap);
        var reducedTypeTuple = Utilities.replaceAll(types, reducedMap);
        return /*pEF.get(v.Word).contains(types)*/reducedTypeSet.contains(reducedTypeTuple);
    }

    private static HashMap<String, HashSet<ArrayList<String>>> EWordPerfectFollowingTypes = null;

    public static HashMap<String, HashSet<ArrayList<String>>> getEWordPerfectFollowingTypes()
    {
        if (EWordPerfectFollowingTypes != null)
            return EWordPerfectFollowingTypes;
        EWordPerfectFollowingTypes = getTypeWordPerfectFollowingTypes("E");
        return EWordPerfectFollowingTypes;
    }

    public static boolean isWordPerfectPrecedingTypes(Graph<WordVertex> tree, WordVertex v)
    {
        getWordPerfectPrecedingTypes();
        var pair = new CustomArrayList<>(new String[]{v.Word, v.Type});
        if (WordPerfectPrecedingTypes.containsKey(pair))
        {
            var reducedMap = getReducedTypeMap();
            var tuples = (Set) Utilities.replaceAll(WordPerfectPrecedingTypes.get(pair),
                    reducedMap
            );
            var inVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                    (x) -> x.Location < v.Location && !isAdverb(tree, x)
            ));
            Utilities.sortBy(inVs, (x) -> x.Location);
            var types = Utilities.replaceAll(Utilities.map((x) -> x.Type, inVs), reducedMap);
            return tuples.contains(types);
        } else return true;
    }

    public static boolean isWordPerfectFollowingTypes(Graph<WordVertex> tree, WordVertex v)
    {
        getWordPerfectFollowingTypes();
        var pair = new CustomArrayList<>(new String[]{v.Word, v.Type});
        if (WordPerfectFollowingTypes.containsKey(pair))
        {
            var reducedMap = getReducedTypeMap();
            var tuples = (Set) Utilities.replaceAll(WordPerfectFollowingTypes.get(pair), reducedMap);
            var inVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                    (x) -> x.Location > v.Location && !isAdverb(tree, x)
            ));
            Utilities.sortBy(inVs, (x) -> x.Location);
            var types = Utilities.replaceAll(Utilities.map((x) -> x.Type, inVs), reducedMap);
            return tuples.contains(types);
        } else return true;
    }

    public static boolean isVerbWordPerfectFollowingTypes(Graph<WordVertex> tree, WordVertex v)
    {
        if (!v.Type.equals("V"))
            return true;
        var pVF = getVerbWordPerfectFollowingTypes();
        if (!pVF.containsKey(v.Word))
            return true;
        var inVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                (x) -> x.Location > v.Location && !isAdverb(tree, x)
        ));
        Utilities.sortBy(inVs, (x) -> x.Location);
        var types = Utilities.map((x) -> x.Type, inVs);
        var reducedMap = getReducedTypeMap();
        var replacedTypeSet = (Set) Utilities.replaceAll(pVF.get(v.Word), reducedMap);
        var replacedTypeTuple = Utilities.replaceAll(types, reducedMap);
        return /*pVF.get(v.Word).contains(types)*/replacedTypeSet.contains(replacedTypeTuple);
    }

    private static HashMap<String, HashSet<ArrayList<String>>> VerbWordPerfectFollowingTypes = null;

    public static HashMap<String, HashSet<ArrayList<String>>> getVerbWordPerfectFollowingTypes()
    {
        if (VerbWordPerfectFollowingTypes != null)
            return VerbWordPerfectFollowingTypes;
        VerbWordPerfectFollowingTypes = getTypeWordPerfectFollowingTypes("V");
        return VerbWordPerfectFollowingTypes;
    }

    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> WordPerfectPrecedingTypes = null;

    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> getWordPerfectPrecedingTypes()
    {
        if (WordPerfectPrecedingTypes != null)
            return WordPerfectPrecedingTypes;
        WordPerfectPrecedingTypes = getWordPerfectConnectingTypes("preceding");
        return WordPerfectPrecedingTypes;
    }

    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> WordPerfectFollowingTypes = null;

    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> getWordPerfectFollowingTypes()
    {
        if (WordPerfectFollowingTypes != null)
            return WordPerfectFollowingTypes;
        WordPerfectFollowingTypes = getWordPerfectConnectingTypes("following");
        return WordPerfectFollowingTypes;
    }

    /**
     * @param loc biến này chỉ có hai giá trị là "following" hoặc "preceding"
     * @return
     */
    public static HashMap<ArrayList<String>, HashSet<ArrayList<String>>> getWordPerfectConnectingTypes(String loc)
    {
        var connectingCounter = new HashMap<ArrayList<String>, HashMap<ArrayList<String>, Integer>>();
        Utilities.executeMathematicaCode("MyObject=%0", connectingCounter);
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                var connectedVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
                        (x) -> (loc.equals("following") ? x.Location > v.Location : x.Location < v.Location)
                                && !isAdverb(tree, x)
                ));
                Utilities.sortBy(connectedVs, (x) -> x.Location);
                var types = Utilities.map((WordVertex x) -> x.Type, connectedVs);
                Utilities.insertValue(connectingCounter, new Object[]{
                        new CustomArrayList<>(new String[]{v.Word, v.Type})
                        , types}, 0, (x) -> x + 1);
            }
        }
        var wordApMean = getWordAppearanceMean();
        var wordApVariance = getWordAppearanceVariance();
        var res = new HashMap<ArrayList<String>, HashSet<ArrayList<String>>>();
        for (var pair : connectingCounter.keySet())
        {
            if (WordAppearances.get(pair.get(0)).containsKey(pair.get(1)))
                if (WordAppearances.get(pair.get(0)).get(pair.get(1)) > wordApMean + wordApVariance)
                {
                    var corres = connectingCounter.get(pair);
                    var values = corres.values();
                    var mean = Utilities.mean(values);
                    /*var variance = Utilities.variance(values);*/
                    var perfectTupleSet = new HashSet<ArrayList<String>>();
                    for (var tuple : corres.keySet())
                        if (corres.get(tuple) >= mean/* + variance*/)
                            perfectTupleSet.add(tuple);
                    res.put(pair, perfectTupleSet);
                }
        }
        /*Utilities.executeMathematicaCode("MyObject=%0",followingCounter);*/
        return res;
    }

    public static HashMap<String, HashSet<ArrayList<String>>> getTypeWordPerfectFollowingTypes(String type)
    {
        var res = new HashMap<String, HashSet<ArrayList<String>>>();
        var auxRes = getWordPerfectFollowingTypes();
        for (var pair : auxRes.keySet())
            if (pair.get(1).equals(type))
                Utilities.insertValue(res,
                        new Object[]{pair.get(0)}, auxRes.get(pair)
                );
        return res;
    }

//    public static HashMap<String, HashSet<ArrayList<String>>> getPerfectPrecedings(String type)
//    {
//        var followingCounter = new HashMap<>();
//        for (var parser : Parsers)
//        {
//            var tree = getDependenceGraph(parser);
//            for (var v : tree.vertexList())
//            {
//                if (v.Type.equals(type))
//                {
//                    var leftVs = Utilities.makeArrayList(Utilities.select(tree.inGoingVertices(v),
//                            (x) -> x.Location < v.Location && !isAdverb(tree, x)
//                    ));
//                    Utilities.sortBy(leftVs, (x) -> x.Location);
//                    var types = Utilities.map((WordVertex x) -> x.Type, leftVs);
//                    Utilities.insertValue(followingCounter, new Object[]{v.Word, types}, 0, (x) -> x + 1);
//                }
//            }
//        }
//        var verbApMean = getWordAppearanceMean() /*Utilities.mean(verbAps)*/;
//        var verbApVariance = getWordAppearanceVariance()/* Utilities.variance(verbAps)*/;
//        var perfectVerbFollows = new HashMap<String, HashSet<ArrayList<String>>>();
//        for (var word : followingCounter.keySet())
//        {
//            if (wordAppearance.get(word).containsKey(type))
//                if (wordAppearance.get(word).get(type) > verbApMean + verbApVariance)
//                {
//                    var corres = (HashMap<ArrayList<String>, Integer>) followingCounter.get(word);
//                    var values = corres.values();
//                    var mean = Utilities.mean(values);
//                    var variance = Utilities.variance(values);
//                    var perfectTupleSet = new HashSet<ArrayList<String>>();
//                    for (var tuple : corres.keySet())
//                        if (corres.get(tuple) > mean/* + variance*/)
//                            perfectTupleSet.add(tuple);
//                    perfectVerbFollows.put((String) word, perfectTupleSet);
//                }
//        }
//        return perfectVerbFollows;
//    }

    public static HashMap<ArrayList<String>, HashMap<String, String>> BalancedTypePairs = null;

    public static HashMap<ArrayList<String>, HashMap<String, String>> getBalancedTypePairs()
    {
        if (BalancedTypePairs != null)
            return BalancedTypePairs;
        var counter = new HashMap<>();
        final var insideStr = "inside";
        final var outsideStr = "outside";
        final var nextStr = "next";
        final var beforeStr = "before";
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var ed : tree.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var dir = v0.Location < v1.Location ? nextStr : beforeStr;
                var inVs = tree.inGoingVertices(v1);
                var outVs = tree.outGoingVertices(v1);
                var pair = new CustomArrayList<>(new String[]{v0.Type, v1.Type});
                if (dir.equals(nextStr))
                {
                    if (Utilities.anyTrue(inVs, (x) -> x.Location > v1.Location && !isAdverb(tree, x)) ||
                            Utilities.anyTrue(outVs, (x) -> x.Location > v1.Location && tree.vertexOutDegree(x) == 0 && x.Type.equals("V")))
                        Utilities.insertValue(counter,
                                new Object[]{pair, dir, insideStr}, 0, (x) -> x + 1
                        );
                    else Utilities.insertValue(counter,
                            new Object[]{pair, dir, outsideStr}, 0, (x) -> x + 1
                    );
                } else
                {
                    if (Utilities.anyTrue(inVs, (x) -> !isAdverb(tree, x) && x.Location < v1.Location) ||
                            Utilities.anyTrue(outVs, x -> x.Location < v1.Location && tree.vertexOutDegree(x) == 0 && x.Type.equals("V")))
                        Utilities.insertValue(counter, new Object[]{pair, dir, insideStr}, 0, (x) -> x + 1);
                    else Utilities.insertValue(counter, new Object[]{pair, dir, outsideStr}, 0, (x) -> x + 1);
                }
            }
        }
        var pairValues = new ArrayList<ArrayList<Integer>>();
        for (var pair : counter.keySet())
            for (var dir : new String[]{nextStr, beforeStr})
            {
                if (Utilities.keySequenceExistsQ(counter, pair, dir))
                {
                    var io = (HashMap<String, Integer>) Utilities.getValue(counter, pair, dir);
                    var insideV = io.containsKey(insideStr) ? io.get(insideStr) : 0;
                    var outsideV = io.containsKey(outsideStr) ? io.get(outsideStr) : 0;
                    var pairV = new CustomArrayList<>(new Integer[]{insideV, outsideV});
                    Utilities.sortBy(pairV, (x) -> x);
                    pairValues.add(pairV);
                }
            }
        var lS = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) pairValues);
        var totalAps = Utilities.map((ArrayList<Integer> x) -> Utilities.sum(x), pairValues);
        var mean = Utilities.mean(totalAps);
        var essentialPairs = new HashMap<ArrayList<String>, HashMap<String, String>>();
        for (var pair : counter.keySet())
            for (var dir : new String[]{nextStr, beforeStr})
            {
                if (Utilities.keySequenceExistsQ(counter, pair, dir))
                {
                    var io = (HashMap<String, Integer>) Utilities.getValue(counter, pair, dir);
                    var insideV = io.containsKey(insideStr) ? io.get(insideStr) : 0;
                    var outsideV = io.containsKey(outsideStr) ? io.get(outsideStr) : 0;
                    if (insideV + outsideV >= mean)
                    {
                        var maxV = Utilities.max(insideV, outsideV);
                        var minV = Utilities.min(insideV, outsideV);
                        if (maxV > lS.get(0) * minV)
                        {
                            var pairOrigin = (ArrayList<String>) pair;
                            Utilities.insertValue(essentialPairs,
                                    new Object[]{pairOrigin, dir},
                                    maxV.equals(insideV) ? insideStr : outsideStr
                            );
                        }
                    }
                }
            }
        BalancedTypePairs = essentialPairs;
        return BalancedTypePairs;
    }

    public static ArrayList<ArrayList<String>> TypePairInsideOutside = null;

    public static ArrayList<ArrayList<String>> getTypePairInsideOutside()
    {
        if (TypePairInsideOutside != null)
            return TypePairInsideOutside;
        var res = new HashMap<>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var ed : tree.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var direction = getEdgeDirection(ed);
                var relative = Utilities.allTrue(tree.inGoingVertices(v0),
                        (x) -> isAdverb(tree, x)
                ) ? "outside" : "inside";
                var typePair = new CustomArrayList<>(new String[]{v0.Type, v1.Type});
                Utilities.insertValue(res, new Object[]{typePair, direction, relative}, 0, (x) -> x + 1);
            }
        }
        var insideOutsideCounter = new ArrayList<ArrayList<Integer>>();
        final var insideStr = "inside";
        final var outsideStr = "outside";
        for (var pair : res.keySet())
            for (var dir : new String[]{"next", "before"})
            {
                if (Utilities.keySequenceExistsQ(res, pair, dir))
                {
                    var insideOutside = (HashMap<String, Integer>) Utilities.getValue(res, pair, dir);
                    var inside = insideOutside.containsKey(insideStr) ? insideOutside.get(insideStr) : 0;
                    var outside = insideOutside.containsKey(outsideStr) ? insideOutside.get(outsideStr) : 0;
                    var valuePair = new CustomArrayList<>(new Integer[]{inside, outside});
                    Utilities.sortBy(valuePair, (x) -> x);
                    insideOutsideCounter.add(valuePair);
                }
            }
        var totalAps = Utilities.map((ArrayList<Integer> ar) -> Utilities.sum(ar), insideOutsideCounter);
        var apMean = Utilities.mean(totalAps);
        var pairRes = new ArrayList<ArrayList<String>>();
        var lS = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) insideOutsideCounter);
        for (var pair : res.keySet())
            for (var dir : new String[]{"next", "before"})
            {
                if (Utilities.keySequenceExistsQ(res, pair, dir))
                {
                    var insideOutside = (HashMap<String, Integer>) Utilities.getValue(res, pair, dir);
                    var inside = insideOutside.containsKey(insideStr) ? insideOutside.get(insideStr) : 0;
                    var outside = insideOutside.containsKey(outsideStr) ? insideOutside.get(outsideStr) : 0;
                    if (inside + outside >= apMean)
                    {
                        var min = Utilities.min(inside, outside);
                        var max = Utilities.max(inside, outside);
                        if (max > min * lS.get(0))
                        {
                            var mainRel = inside > outside ? "inside" : "outside";
                            var pairOrigin = (ArrayList<String>) pair;
                            pairRes.add(new CustomArrayList<>(new String[]{pairOrigin.get(0), pairOrigin.get(1),
                                    dir, mainRel}));
                        }
                    }
                }
            }
        TypePairInsideOutside = pairRes;
        return TypePairInsideOutside;
    }

    public static HashMap<ArrayList<Integer>, Integer> EdgeValidities;

//    public static HashMap<ArrayList<Integer>, Integer> getEdgeValidities()
//    {
//        var res = new HashMap<ArrayList<Integer>, Integer>();
//        /*UnaryFunction<Boolean, Integer> func = (x) -> x ? 1 : 0;*/
//        var progress = new ProgressIndicator(0, Parsers.size() - 1);
//        progress.setDelay(1000);
//        progress.show();
//        for (var i = 0; i <= Parsers.size() - 1; i++)
//        {
//            if (progress.Stopped)
//                break;
//            progress.setValue(i);
//            var parser = Parsers.get(i);
//            var g = getDependenceGraph(parser);
//            for (var ed : g.edgeList())
//            {
//                /*var aux = new CustomArrayList<>(
//                        new Integer[]{
//                                func.apply(isSensibleEdge(ed)),
//                                func.apply(isSensibleEdge(ed, "tail")),
//                                func.apply(isSensibleEdge(ed, "head")),
//                                func.apply(isInComingSensibleEdge(ed))
//                        }
//                );*/
//                var aux = getEdgeValidity(ed);
//                if (!res.containsKey(aux))
//                    res.put(aux, 0);
//                res.put(aux, res.get(aux) + 1);
//            }
//        }
//        return res;
//    }

    public static <T> void pageRankTopologicalSort(ArrayList<T> list, BinaryFunction<T, T, ? extends Number> comparator)
    {
        var g = new Graph<T>();
        g.addVertices(list);
        for (var i = 0; i <= list.size() - 2; i++)
        {
            var iEle = list.get(i);
            for (var j = i + 1; j <= list.size() - 1; j++)
            {
                var jEle = list.get(j);
                var comp = comparator.apply(iEle, jEle).doubleValue();
                if (comp < 0)
                    g.addEdge(iEle, jEle);
                else if (comp > 0)
                    g.addEdge(jEle, iEle);
            }
        }
        Utilities.map((ArrayList<T> ed) -> g.setEdgeWeight(ed, 1d), g.edgeList());
        var opts = new HashMap<String, Object>();
        opts.put("Step Number", 100);
        opts.put("Show Progress", false);
        var pR = Graph.pageRank(g, opts);
        Utilities.sortBy(list, (x) -> pR.get(x));
    }

    public static boolean isWordConnectingSensibleEdge(ArrayList<WordVertex> ed, String loc)
    {
        return isWordConnectingSensibleEdge(ed, loc, WordConnectingExamination.Mean);
    }

    public static boolean isWordConnectingSensibleEdge(ArrayList<WordVertex> ed, String loc, WordConnectingExamination examination /*boolean perfectType*/)
    {
        HashMap comingTypes;
        if (loc.equals("incoming"))
            comingTypes = getWordIncomingTypes();
        else comingTypes = getWordOutcomingTypes();
        WordVertex v0, v1;
        if (loc.equals("incoming"))
        {
            v0 = ed.get(0);
            v1 = ed.get(1);
        } else
        {
            v0 = ed.get(1);
            v1 = ed.get(0);
        }
        var direction = getEdgeDirection(ed);
        var reducedCorres = getReducedTypeMap();
        if (!Utilities.keySequenceExistsQ(comingTypes, v1.Word))
            return true;
        var typeCounter = (HashMap<String, HashMap<String, HashMap<String, Integer>>>) comingTypes.get(v1.Word);
        var reducedTypeCounter = new HashMap<String, HashMap<String, HashMap<String, Integer>>>();
        for (var type0 : typeCounter.keySet())
            for (var dir : typeCounter.get(type0).keySet())
                if (dir.equals("undefined"))
                    continue;
                else
                    for (var type1 : typeCounter.get(type0).get(dir).keySet())
                    {
                        Utilities.insertValue(reducedTypeCounter,
                                new Object[]{/*reducedCorres.get(type0)*/type0, dir, reducedCorres.get(type1)},
                                0, (x) -> x + typeCounter.get(type0).get(dir).get(type1)
                        );
                    }
        var v1Type = v1.Type/*reducedCorres.get(v1.Type)*/;
        if (!Utilities.keySequenceExistsQ(reducedTypeCounter, v1Type))
            return true;
        if (!Utilities.keySequenceExistsQ(reducedTypeCounter, v1Type, direction))
            return false;
        var appearanceCounter = reducedTypeCounter.get(v1Type).get(direction);
        var reducedV0Type = reducedCorres.get(v0.Type);
        var reducedV0TypeCount = appearanceCounter.containsKey(reducedV0Type) ? appearanceCounter.get(reducedV0Type) : 0;
        switch (examination)
        {
            case Mean:
            {
                var values = Utilities.makeArrayList(appearanceCounter.values());
                var mean = Utilities.mean(values);
                return reducedV0TypeCount >= Utilities.min((loc.equals("incoming") ? getWordIncomingAppearanceMean() :
                                getWordOutcomingAppearanceMean()),
                        mean
                );
            }
            case DirectionMax:
            {
//                var maxType = Utilities.maxBy(appearanceCounter.keySet(), x -> appearanceCounter.get(x));
//                return appearanceCounter.get(maxType).equals(reducedV0TypeCount);
                var maxValue = Utilities.max((ArrayList<Integer>) (Object) getLeafValues(appearanceCounter));
                return maxValue.equals(reducedV0TypeCount);
            }
            default:
            {
                var maxValue = Utilities.max((ArrayList<Integer>) (Object) getLeafValues(reducedTypeCounter.get(v1Type)));
                return maxValue.equals(reducedV0TypeCount);
            }
        }
    }

    public static boolean isWordOutcomingSensibleEdge(ArrayList<WordVertex> ed)
    {
        var v = ed.get(0);
        var appMean = getWordAppearanceMean();
        if (WordAppearances.get(v.Word).get(v.Type) < appMean)
            return true;
        return isWordConnectingSensibleEdge(ed, "outcoming");
    }

    public static boolean isWordOutcomingNonDirectionPerfectTypeSensibleEdge(ArrayList<WordVertex> ed)
    {
        var v = ed.get(0);
        var appMean = getWordAppearanceMean();
        if (WordAppearances.get(v.Word).get(v.Type) < appMean)
            return true;
        return isWordConnectingSensibleEdge(ed, "outcoming", WordConnectingExamination.NonDirectionMax /*true*/);
    }

    public static boolean isWordOutcomingPerfectTypeSensibleEdge(ArrayList<WordVertex> ed)
    {
        var v = ed.get(0);
        var appMean = getWordAppearanceMean();
        if (WordAppearances.get(v.Word).get(v.Type) < appMean)
            return true;
        return isWordConnectingSensibleEdge(ed, "outcoming", WordConnectingExamination.DirectionMax /*true*/);
    }

    public static boolean isWordIncomingSensibleEdge(ArrayList<WordVertex> ed)
    {
        var v = ed.get(1);
        var appMean = getWordAppearanceMean();
        if (WordAppearances.get(v.Word).get(v.Type) < appMean)
            return true;
        return isWordConnectingSensibleEdge(ed, "incoming");
    }

    public static boolean isWordIncomingNonDirectionPerfectTypeSensibleEdge(ArrayList<WordVertex> ed)
    {
        var v = ed.get(1);
        var appMean = getWordAppearanceMean();
        if (WordAppearances.get(v.Word).get(v.Type) < appMean)
            return true;
        return isWordConnectingSensibleEdge(ed, "incoming", WordConnectingExamination.NonDirectionMax /*true*/);
    }

    public static boolean isWordIncomingPerfectTypeSensibleEdge(ArrayList<WordVertex> ed)
    {
        var v = ed.get(1);
        var appMean = getWordAppearanceMean();
        if (WordAppearances.get(v.Word).get(v.Type) < appMean)
            return true;
        return isWordConnectingSensibleEdge(ed, "incoming", WordConnectingExamination.DirectionMax /*true*/);
    }

    public static HashMap WordOutcomingTypes;

    public static HashMap getWordOutcomingTypes()
    {
        if (WordOutcomingTypes != null)
            return WordOutcomingTypes;
        WordOutcomingTypes = getWordConnectingTypes("outcoming");
        return WordOutcomingTypes;
    }

    /**
     * cấu trúc của biến này là word->Type->Direction->counter
     */
    public static HashMap WordIncomingTypes;

    public static HashMap getWordIncomingTypes()
    {
        if (WordIncomingTypes != null)
            return WordIncomingTypes;
        WordIncomingTypes = getWordConnectingTypes("incoming");
        return WordIncomingTypes;
    }

    public static HashMap getWordConnectingTypes(String loc)
    {
        var res = new HashMap();
        final String undefinedStr = "undefined";
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var ed : tree.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var direction = getEdgeDirection(ed);
                if (loc.equals("incoming"))
                {
//                    if (!isAdverb(tree, v0))
                    Utilities.insertValue(res,
                            new Object[]{v1.Word, v1.Type, direction, v0.Type},
                            0,
                            (x) -> x + 1
                    );
                    if (tree.vertexInDegree(v0) == 0)
                        Utilities.insertValue(res,
                                new Object[]{v0.Word, v0.Type, undefinedStr},
                                0, (x) -> x + 1
                        );
                } else
                {
//                    if (!isAdverb(tree, v1))
                    Utilities.insertValue(res,
                            new Object[]{v0.Word, v0.Type, direction, v1.Type},
                            0,
                            (x) -> x + 1
                    );
                    if (tree.vertexOutDegree(v1) == 0)
                        Utilities.insertValue(res,
                                new Object[]{v1.Word, v1.Type, undefinedStr},
                                0, (x) -> x + 1
                        );
                }
            }
        }
        return res;
    }

    /**
     * cấu trúc của biến này là {type0,type1}->direction->tailOrHead->counter
     */
    public static HashMap<ArrayList<String>, HashMap<String, HashMap<String, HashMap<String, Integer>>>> TypePairWordApperance;

    public static void initializeTypePairWordApperance()
    {
        TypePairWordApperance = new HashMap<>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            for (var ed : g.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var typePair = new CustomArrayList<>(new String[]{v0.Type, v1.Type});
                var direction = v0.Location < v1.Location ? "next" : "before";
                for (var loc : new String[]{"tail", "head"})
                    if (!Utilities.keySequenceExistsQ(TypePairWordApperance, typePair, direction, loc))
                        Utilities.insertValue(TypePairWordApperance, new Object[]{typePair, direction, loc},
                                new HashMap<String, Integer>()
                        );
                for (var loc : new String[]{"tail", "head"})
                {
                    var counter = (HashMap<String, Integer>) Utilities.getValue(TypePairWordApperance, typePair, direction, loc);
                    var insertedWord = loc.equals("tail") ? v0.Word : v1.Word;
                    if (!counter.containsKey(insertedWord))
                        counter.put(insertedWord, 0);
                    counter.put(insertedWord, counter.get(insertedWord) + 1);
                }
            }
        }
    }

    public static HashMap<WordVertex, ArrayList<Integer>> assignTreeCoordinate(Graph<WordVertex> tree)
    {
        var res = new HashMap<WordVertex, ArrayList<Integer>>();
        if (tree.vertexCount() == 0)
            return res;
        if (tree.vertexCount() == 1)
        {
            var v = Utilities.getFirstElement(tree.vertexList());
            res.put(v, new ArrayList<>());
            return res;
        }
        var root = getRoot(tree);
        var inVs = Utilities.makeArrayList(tree.inGoingVertices(root));
        Utilities.sortBy(inVs, (x) -> x.Location);
        res.put(root, new ArrayList<>());
        for (var i = 0; i <= inVs.size() - 1; i++)
        {
            var v = inVs.get(i);
            var subTree = tree.subgraph(tree.vertexInComponent(v));
            var subRes = assignTreeCoordinate(subTree);
            for (var w : subRes.keySet())
            {
                var coor = subRes.get(w);
                var copied = Utilities.makeArrayList(coor);
                copied.add(0, i);
                res.put(w, copied);
            }
        }
        return res;
    }

    public static Graph<WordVertex> adjustLeaves(Graph<WordVertex> g, Graph<WordVertex> tree)
    {
        var treeVs = tree.vertexList();
        var leaves = Utilities.select(tree.vertexList(),
                (x) -> tree.vertexInDegree(x) == 0
        );
        var addVs = Utilities.select(g.vertexList(),
                (x) -> Utilities.anyTrue(leaves,
                        (y) -> y.Location == x.Location
                )
        );
        var newVs = Utilities.union(tree.vertexList(), addVs);
        var opts = new HashMap<String, Object>();
        opts.put("Excluded Processed Vertices", addVs);
        opts.put("cycleDetection", false);
        var subG = g.subgraph(newVs);
        return strongRecursiveMaxTree(subG, opts);
    }

    public static double leafEdgeVertexRankVariance(Graph<WordVertex> tree)
    {
        var nextLs = vertexToEdgeRankLeastSquares(EdgePR, VertexPR, "next", new AtomicReference<>());
        var beforeLs = vertexToEdgeRankLeastSquares(EdgePR, VertexPR, "before", new AtomicReference<>());
        var data = new ArrayList<Double>();
        var meanRank = leafEdgeVertexRankMean();
        UnaryFunction<WordVertex, ArrayList<String>> getPair = (x) ->
        {
            return new CustomArrayList<>(new String[]{x.Word, x.Type});
        };
        for (var v0 : tree.vertexList())
        {
            if (tree.vertexInDegree(v0) == 0 && tree.vertexOutDegree(v0) != 0)
            {
                var v1 = Utilities.getFirstElement(tree.outGoingVertices(v0));
                var direction = v0.Location < v1.Location ? "next" : "before";
                var edgeV = new EdgeVertex(
                        getPair.apply(v0),
                        getPair.apply(v1)
                );
                edgeV.Direction = direction;
                if (EdgePR.containsKey(edgeV))
                {
                    /*System.out.println("accepted edge vertex");*/
                    data.add(EdgePR.get(edgeV));
                } else
                {
                    var rank0 = VertexPR.get(getPair.apply(v0));
                    var rank1 = VertexPR.get(getPair.apply(v1));
                    switch (direction)
                    {
                        case "next":
                            var value = nextLs.get(0) * rank0 + nextLs.get(1) * rank1;
                            data.add(value);
                            break;
                        case "before":
                            value = beforeLs.get(0) * rank0 + beforeLs.get(1) * rank1;
                            data.add(value);
                            break;
                    }
                }
            }
        }
        /*System.out.println("data "+data);*/
        var sum = 0d;
        for (var value : data)
            sum += (value - meanRank) * (value - meanRank);
        return Math.sqrt(sum / data.size());
        /*return sum;*/
    }

    private static Double LeafEdgeVertexRankMean = null;

    public static double leafEdgeVertexRankMean()
    {
        if (LeafEdgeVertexRankMean != null)
            return LeafEdgeVertexRankMean;
        var data = new ArrayList<Double>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            for (var v0 : g.vertexList())
            {
                if (g.vertexInDegree(v0) == 0 && g.vertexOutDegree(v0) > 0)
                {
                    var v1 = Utilities.getFirstElement(g.outGoingVertices(v0));
                    var edgeV = new EdgeVertex(
                            new CustomArrayList<>(new String[]{v0.Word, v0.Type}),
                            new CustomArrayList<>(new String[]{v1.Word, v1.Type})
                    );
                    edgeV.Direction = v0.Location < v1.Location ? "next" : "before";
                    data.add(EdgePR.get(edgeV));
                }
            }
        }
        LeafEdgeVertexRankMean = Utilities.mean(data);
        return LeafEdgeVertexRankMean;
    }

    public static double leafRankVariance(Graph<WordVertex> tree)
    {
        var rankMean = leafRankMean();
        var ranks = leafRanks(tree);
        var sum = 0d;
        for (var rank : ranks)
            sum += (rank - rankMean) * (rank - rankMean);
        return Math.sqrt(sum / ranks.size());
        /*return sum;*/
    }

    private static Double LeafRankMean = null;

    public static double leafRankMean()
    {
        if (LeafRankMean != null)
            return LeafRankMean;
        var data = new ArrayList<Double>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            var ranks = leafRanks(g);
            data.addAll(ranks);
        }
        LeafRankMean = Utilities.mean(data);
        return LeafRankMean;
    }

    public static ArrayList<Double> leafRanks(Graph<WordVertex> tree)
    {
        var res = new ArrayList<Double>();
        var leaves = Utilities.select(tree.vertexList(),
                (x) -> tree.vertexInDegree(x) == 0
        );
        for (var leaf : leaves)
        {
            var pair = new CustomArrayList<>(new String[]{leaf.Word, leaf.Type});
            var r = VertexPR.get(pair);
            res.add(r);
        }
        return res;
    }

    public static boolean isSentenceToRootValid(Graph<WordVertex> tree)
    {
        var root = getRoot(tree);
        var rightTree = tree.subgraph(Utilities.select(tree.vertexList(),
                (x) -> x.Location >= root.Location)
        );
        if (root.Type.equals("V"))
        {
            var selectedVs = Utilities.select(tree.vertexList(),
                    (x) -> x.Location > root.Location && isSentenceAt(tree, x)
            );
            for (var v : selectedVs)
            {
                var path = tree.findPath(v, root);
                var between = Utilities.part(path, 1, path.size() - 1);
                if (Utilities.allTrue(between, (x) -> rightTree.vertexInDegree(x) == 1))
                    return false;
            }
        }
        return true;
    }

    public static boolean isSentenceAt(Graph<WordVertex> tree, WordVertex v)
    {
        if (!v.Type.equals("V"))
            return false;
        var inVs = tree.inGoingVertices(v);
        var wm = getWordMeaningType(tree);
        return Utilities.anyTrue(inVs,
                (x) -> x.Location < v.Location && wm.get(x).equals("N")
        ) && Utilities.anyTrue(inVs,
                (x) -> x.Location > v.Location && Utilities.anyTrue(tree.vertexInComponent(x),
                        (y) -> wm.get(y).equals("N")
                )
        );
    }

    public static HashSet<WordVertex> adjustTypes2(Graph<WordVertex> g, Graph<WordVertex> tree)
    {
        var copiedG = g.clone();
        UnaryFunction<WordVertex, ArrayList<String>> getPair = (x) -> new CustomArrayList<String>(new String[]{x.Word, x.Type});
        var leaves = Utilities.makeHashSet(Utilities.select(tree.vertexList(),
                        (x) ->
                        {
                            var check0 = tree.vertexInDegree(x) == 0;
                            if (!check0)
                                return false;
                            var sameLocs = Utilities.select(copiedG.vertexList(),
                                    (y) -> y.Location == x.Location
                            );
                            var ranks = Utilities.map((WordVertex y) -> VertexPR.get(getPair.apply(y)),
                                    sameLocs);
                            var rankMean = Utilities.mean(ranks);
                            return VertexPR.get(getPair.apply(x)) > rankMean;
                        }
                )
        );
//        System.out.println("selected leaves "+leaves);
//        var gVs = g.vertexList();
//        var removedLeaves = Utilities.select(leaves,
//                (x) -> Utilities.anyTrue(gVs,
//                        (y) -> y.Location == x.Location && !x.equals(y) && !isEssentialInsideWordQ(y)
//                )
//        );
//        copiedG.deleteVertices(removedLeaves);
        var removedEds = Utilities.select(copiedG.edgeList(),
                (ed) -> leaves.contains(ed.get(1))
        );
        copiedG.deleteEdges(removedEds);
        var newTypes = Utilities.makeHashSet(decideVertexTypes(copiedG, true));
        var oldTypes = Utilities.makeHashSet(tree.vertexList());
        if (newTypes.equals(oldTypes))
            return null;
        else return newTypes;
    }

    public static HashSet<WordVertex> adjustTypes(Graph<WordVertex> g, Graph<WordVertex> tree)
    {
        var wg = g.clone();
        Utilities.map((ArrayList<WordVertex> ed) ->
        {
            tree.setEdgeWeight(ed, wg.getEdgeWeight(ed));
        }, tree.edgeList());
        var opts = new HashMap<String, Object>();
        opts.put("Step Number", 200);
        opts.put("Show Progress", false);
        var pR = Graph.pageRank(tree, opts);
        var vs = Utilities.makeArrayList(pR.keySet());
        Utilities.topologicalSort(vs,
                (x, y) ->
                {
                    var pairX = new ArrayList<Double>();
                    pairX.add(-((double) toRootDistance(tree, x)));
                    var apX = WordAppearances.get(x.Word).get(x.Type).doubleValue();
                    pairX.add(pR.get(x) * apX);
                    var pairY = new ArrayList<Double>();
                    pairY.add(-((double) toRootDistance(tree, y)));
                    var apY = WordAppearances.get(y.Word).get(y.Type).doubleValue();
                    pairY.add(pR.get(y) * apY);
                    return Utilities.lexicographicOrder(pairX, pairY, (u, v) -> u - v);
                }
        );
        vs = (ArrayList<WordVertex>) (Object) Utilities.reverse(vs);
        var treeVs = tree.vertexList();
        for (var v : vs)
        {
            cutGraph(wg, v);
            var newTypes = decideVertexTypes(wg);
            if (!Utilities.containsAll(treeVs, newTypes))
            {
                var res = Utilities.join(newTypes, treeVs);
                res = Utilities.deleteDuplicates(res,
                        (x, y) -> x.Location == y.Location
                );
                return Utilities.makeHashSet(res);
            }
        }
        return null;
    }

    public static ArrayList<WordVertex> decideVertexTypes(Graph<WordVertex> g)
    {
        return decideVertexTypes(g, false);
    }

    public static ArrayList<WordVertex> decideVertexTypes(Graph<WordVertex> g, boolean requireAVerb)
    {
        var copiedG = g.clone();
        makeIdealEdgeRank(copiedG);
        return recursiveChooseVertexTypes(copiedG, requireAVerb);
    }

    public static void makeIdealEdgeRank(Graph<WordVertex> g)
    {
        var nextLs = vertexToEdgeRankLeastSquares(EdgePR, VertexPR, "next", new AtomicReference<>());
        var beforeLs = vertexToEdgeRankLeastSquares(EdgePR, VertexPR, "before", new AtomicReference<>());
        for (var ed : g.edgeList())
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            var w0 = g.getVertexWeight(v0);
            var w1 = g.getVertexWeight(v1);
            var direction = v0.Location < v1.Location ? "next" : "before";
            if (direction.equals("next"))
                g.setEdgeWeight(ed, w0 * nextLs.get(0) + w1 * nextLs.get(1));
            else g.setEdgeWeight(ed, w0 * beforeLs.get(0) + w1 * beforeLs.get(1));
        }
    }

    public static ArrayList<WordVertex> recursiveChooseVertexTypes(Graph<WordVertex> g, boolean requireAVerb)
    {
        if (g.vertexCount() == 0)
            return new ArrayList<WordVertex>();
        var wg = g.clone();
        var opts = new HashMap<String, Object>();
        opts.put("Step Number", 200);
        opts.put("Show Progress", false);
        var res = new ArrayList<WordVertex>();
        var maxIndex = Utilities.max(Utilities.map((WordVertex x) -> x.Location, g.vertexList()));
        while (wg.vertexCount() > 0)
        {
            var pR = Graph.pageRank(wg, opts);
            var groups = Utilities.gatherBy(wg.vertexList(), (x) -> x.Location);
            var collectedVs = new ArrayList<WordVertex>();
            for (var group : groups)
            {
                var groupAr = Utilities.makeArrayList(group);
                Utilities.quickSort(groupAr,
                        (x, y) ->
                        {
                            var pairX = new ArrayList<Double>();
                            var pairY = new ArrayList<Double>();
                            var apX = WordAppearances.get(x.Word).get(x.Type).doubleValue();
                            pairX.add(pR.get(x) * apX);
                            pairX.add(apX);
                            var apY = WordAppearances.get(y.Word).get(y.Type).doubleValue();
                            pairY.add(pR.get(y) * apY);
                            pairY.add(apY);
                            return Utilities.lexicographicOrder(pairX, pairY, (u, v) -> u - v);
                        }
                );
                collectedVs.add(Utilities.getLastElement(groupAr));
            }
            Utilities.quickSort(collectedVs,
                    (x, y) -> pR.get(x) - pR.get(y)
            );
            var chosenV = Utilities.getLastElement(collectedVs);
            res.add(chosenV);
            cutGraph(wg, chosenV);
        }
        if (requireAVerb)
            if (Utilities.anyTrue(g.vertexList(), (x) -> x.Type.equals("V") && x.Location < maxIndex))
                if (!Utilities.anyTrue(res, (x) -> x.Type.equals("V") && x.Location < maxIndex))
                {
                    wg = g.clone();
                    var pR = Graph.pageRank(wg, opts);
                    var verbs = Utilities.select(wg.vertexList(), (x) -> x.Type.equals("V"));
                    var maxVerbs = Utilities.maximals(verbs, (x, y) ->
                    {
                        var pairX = new CustomArrayList<Double>(new Double[]{
                                pR.get(x),
                                -(double) x.Location
                        });
                        var pairY = new CustomArrayList<Double>(new Double[]{
                                pR.get(y),
                                -(double) y.Location
                        });
                        return Utilities.lexicographicOrder(pairX, pairY, (u, v) -> u - v);
                    });
                    var maxVerb = Utilities.getFirstElement(maxVerbs);
                    wg.deleteVertices(Utilities.select(wg.vertexList(), (x) ->
                    {
                        return x.Location == maxVerb.Location && !x.equals(maxVerb);
                    }));
                    return recursiveChooseVertexTypes(wg, false);
                }
        return res;
    }

    public static void cutGraph(Graph<WordVertex> g, WordVertex v)
    {
        var removedVs = Utilities.select(g.vertexList(),
                (x) -> x.Location == v.Location
        );
        var removedEds = Utilities.select(g.edgeList(),
                (ed) ->
                {
                    var v0 = ed.get(0);
                    var v1 = ed.get(1);
                    return (v0.Location < v.Location && v.Location < v1.Location) || (v1.Location < v.Location && v.Location < v0.Location);
                }
        );
        g.deleteVertices(removedVs);
        /*g.deleteEdges(removedEds);*/
    }

    public static Graph<WordVertex> strongGraphClone(Graph<WordVertex> g)
    {
        var res = new Graph<WordVertex>();
        for (var v : g.vertexList())
        {
            var copiedV = (WordVertex) v.clone();
            res.addVertex(copiedV);
            res.setVertexWeight(copiedV, g.getVertexWeight(v));
        }
        for (var ed : g.edgeList())
        {
            res.addEdge(ed);
            res.setEdgeWeight(ed, g.getEdgeWeight(ed));
        }
        return res;
    }

    public static Graph<WordVertex> makeRootDependenceGraph(Graph<WordVertex> g)
    {
        return makeRootDependenceGraph(g, true);
    }

    public static Graph<WordVertex> makeRootDependenceGraph(Graph<WordVertex> g, boolean isParallel)
    {
        var res = new Graph<WordVertex>();
        Utilities.map((WordVertex x) ->
        {
            res.addVertex(x);
        }, g.vertexList());
        var myStream = new ArrayList<ArrayList<Object>>();
        for (var v : g.vertexList())
        {
            var copiedG = strongGraphClone(g);
            var copiedV = Utilities.firstCase(copiedG.vertexList(),
                    (x) -> x.equals(v)
            );
            myStream.add(
                    new CustomArrayList<Object>(new Object[]{
                            copiedG, copiedV
                    })
            );
        }
        Function<ArrayList<Object>, ArrayList<ArrayList<WordVertex>>> func = (pair) ->
        {
            var copiedG = (Graph<WordVertex>) pair.get(0);
            var root = (WordVertex) pair.get(1);
            var opts = new HashMap<String, Object>();
            opts.put("cycleDetection", false);
            var maxTree = maximumSpanningTree(copiedG, root, opts);
            var inVs = maxTree.inGoingVertices(root);
            var partialRes = new ArrayList<ArrayList<WordVertex>>();
            for (var x : inVs)
                partialRes.add(new CustomArrayList<>(
                        new WordVertex[]{x, root}
                ));
            return partialRes;
        };
        if (isParallel)
            myStream.parallelStream().map(func).forEachOrdered((eds) ->
            {
                for (var ed : eds)
                    res.addEdge(ed);
            });
        else myStream.stream().map(func).forEachOrdered((eds) ->
        {
            for (var ed : eds)
                res.addEdge(ed);
        });
        return res;
    }

    public static boolean isTrustedEdge(ArrayList<WordVertex> ed)
    {
        return isSensibleEdge(ed) && isWordOutcomingSensibleEdge(ed) && isWordIncomingSensibleEdge(ed);
    }

    public static boolean isEssentialEdgeLocation(ArrayList<WordVertex> ed, String location)
    {
        var typePIO = getTypePairInsideOutside();
        var ternary = new CustomArrayList<>(new String[]{ed.get(0).Type, ed.get(1).Type, getEdgeDirection(ed)});
        for (var loc : new String[]{"inside", "outside"})
        {
            var fournary = (ArrayList<String>) Utilities.append(ternary, loc);
            if (typePIO.contains(fournary) && loc.equals(location))
                return true;
        }
        return false;
    }

    public static boolean isEssentialOutsideEdge(ArrayList<WordVertex> ed)
    {
        return isEssentialEdgeLocation(ed, "outside");
    }

    public static boolean isEssentialInsideEdge(ArrayList<WordVertex> ed)
    {
        return isEssentialEdgeLocation(ed, "inside");
    }

    final static String essentialInsideStr = "essentialInside";
    final static String essentialOutsideStr = "essentialOutside";
    /*final static String trustedEdgeStr = "trustedEdge";*/
//    final static String insideBalancedTypePairStr = "insideBalancedTypePair";
//    final static String outsideBalancedTypePairStr = "outsideBalancedTypePair";
//    final static String essentialInsideEdgeStr = "essentialInsideEdge";
//    final static String essentialOutsideEdgeStr = "essentialOutsideEdge";
    //    final static String isVerbWordPerfectFollowingTypesStr = "isVerbWordPerfectFollowingTypes";
//    final static String isEWordPerfectFollowingTypesStr = "isEWordPerfectFollowingTypes";
    //    final static String isWordPerfectFollowingTypesStr = "isWordPerfectFollowingTypes";
//    final static String isWordPerfectPrecedingTypesStr = "isWordPerfectPrecedingTypes";
    final static String isSensibleEdgeStr = "isSensibleEdge";
    //    final static String isWordIncomingSensibleEdgeStr = "isWordIncomingSensibleEdge";
//    final static String isWordIncomingPerfectTypeSensibleEdgeStr = "isWordIncomingPerfectTypeSensibleEdge";
//    final static String isWordIncomingNonDirectionPerfectTypeSensibleEdgeStr = "isWordIncomingNonDirectionPerfectTypeSensibleEdge";
    //    final static String isWordOutcomingSensibleEdgeStr = "isWordOutcomingSensibleEdge";
//    final static String isWordOutcomingPerfectTypeSensibleEdgeStr = "isWordOutcomingPerfectTypeSensibleEdge";
//    final static String isWordOutcomingNonDirectionPerfectTypeSensibleEdgeStr = "isWordOutcomingNonDirectionPerfectTypeSensibleEdge";
//    final static String isTypePerfectAttachingStr = "isTypePerfectAttaching";
    final static String isTypePerfectFollowingTypesErrorStr = "isTypePerfectFollowingTypesErrors";
    final static String isTypePerfectPrecedingTypesErrorStr = "isTypePerfectPrecedingTypesErrors";
    final static String isMissingNounStr = "isMissingNoun";
    //    final static String isClosestToRootEndingErrorsStr = "isClosestToRootEndingErrors";
//    final static String isAdjectiveToVerbErrorsStr = "isAdjectiveToVerbErrors";
    //    final static String isNounMeaningSupplementErrorsStr = "isNounMeaningSupplementErrors";
    final static String isCloseSeparationErrorsStr = "isCloseSeparationErrors";
    final static String isTernaryLocalErrorsStr = "isTernaryLocalErrors";
    final static String isPronounAdverbPropertyErrorsStr = "isPronounAdverbPropertyErrors";
    final static String isEssentialOutsideTypeErrorsStr = "isEssentialOutsideTypeErrors";

    public static HashMap<String, Object> countErrors(Graph<WordVertex> tree)
    {
        var res = nonMeaningEdgeConnectedCountErrors(new Graph<WordVertex>());
        var copiedTree = tree.clone();
        if (copiedTree instanceof Parser)
            ((Parser) copiedTree).deleteMeaningSupplementEdges();
        var composes = copiedTree.weaklyConnectedComponents();
        Utilities.map(
                compos ->
                {
                    var subRes = nonMeaningEdgeConnectedCountErrors(copiedTree.subgraph(compos));
                    Utilities.insertValues(res, subRes,
                            () -> new HashSet<>(),
                            (HashSet x, HashSet y) ->
                            {
                                x.addAll(y);
                                return x;
                            }
                    );
                }
                , composes);
        return res;
    }

    public static HashMap<String, Object> nonMeaningEdgeConnectedCountErrors(Graph<WordVertex> tree)
    {
        var res = new HashMap<String, Object>();
        for (var name : new String[]{/*essentialInsideStr, essentialOutsideStr,*/
                isSensibleEdgeStr,/* isTypePerfectAttachingStr,*/ isTypePerfectFollowingTypesErrorStr,
                isTypePerfectPrecedingTypesErrorStr, isMissingNounStr, /*isClosestToRootEndingErrorsStr,*/
                /*isAdjectiveToVerbErrorsStr,*/ isCloseSeparationErrorsStr, isTernaryLocalErrorsStr,
                isPronounAdverbPropertyErrorsStr, isEssentialOutsideTypeErrorsStr})
            Utilities.insertValue(res,
                    new Object[]{name}, new HashSet<>()
            );
        for (var v : tree.vertexList())
        {
            if (isEssentialOutsideTypeError(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isEssentialOutsideTypeErrorsStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
            if (isPronounAdverbPropertyError(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isPronounAdverbPropertyErrorsStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
            if (isTernaryLocalError(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isTernaryLocalErrorsStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
            if (isCloseSeparationError(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isCloseSeparationErrorsStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
            if (isTypePerfectPrecedingTypesError(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isTypePerfectPrecedingTypesErrorStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
            if (isTypePerfectFollowingTypesError(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isTypePerfectFollowingTypesErrorStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
            if (isMissingNoun(tree, v))
                Utilities.insertValue(res,
                        new Object[]{isMissingNounStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(v);
                            return x;
                        }
                );
//            if (isWordOutside(tree, v) && isEssentialInsideWordQ(v))
//                ((HashSet) res.get(essentialInsideStr)).add(v);
//            if (isWordInside(tree, v) && isEssentialOutsideWordQ(v))
//                ((HashSet) res.get(essentialOutsideStr)).add(v);
        }
        for (var ed : tree.edgeList())
        {
//            if (!isTypePerfectAttaching(ed))
//                Utilities.insertValue(res,
//                        new Object[]{isTypePerfectAttachingStr},
//                        new HashSet<>(),
//                        (x) ->
//                        {
//                            x.add(ed);
//                            return x;
//                        }
//                );

            if (!isSensibleEdge(ed))
                Utilities.insertValue(res,
                        new Object[]{isSensibleEdgeStr},
                        new HashSet<>(),
                        (x) ->
                        {
                            x.add(ed);
                            return x;
                        }
                );
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            var dir = getEdgeDirection(ed);
        }
        return res;
    }

    public static void sentenceModifyTree(Graph<WordVertex> tree, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var wm = getWordMeaningType(tree);
        var vs = Utilities.makeArrayList(tree.vertexList());
        Utilities.topologicalSort(vs,
                (x, y) ->
                {
                    var path = tree.findPath(x, y);
                    if (path != null)
                        return -1;
                    path = tree.findPath(y, x);
                    if (path != null)
                        return 1;
                    return 0;
                }
        );
        for (var v : vs)
        {
            if (tree.vertexOutDegree(v) == 0)
                continue;
            var inCompos = tree.vertexInComponent(v);
            if (Utilities.anyTrue(processedGroups, (x) -> Utilities.containsAll(x, inCompos)))
                continue;
            NullAction seenAction = () ->
            {
                Utilities.map((WordVertex x) ->
                {
                    x.isMarked = false;
                    x.isProcessedVertex = false;
                    x.isAdditionalProcessedVertex = false;
                }, inCompos);
                v.isMarked = true;
            };
            if (v.Type.equals("V"))
            {
                var inVs = Utilities.makeHashSet(Utilities.select(tree.inGoingVertices(v),
                        (x) -> x.Location < v.Location
                ));
                var check = Utilities.anyTrue(inVs,
                        (x) -> wm.get(x).equals("N")
                );
                if (check)
                {
                    seenAction.apply();
                    Utilities.map((WordVertex x) ->
                    {
                        if (wm.get(x).equals("N"))
                            x.isAdditionalProcessedVertex = true;
                    }, inVs);
                    return;
                }
            }
            if (wm.get(v).equals("N"))
            {
                var inVs = Utilities.makeHashSet(Utilities.select(tree.inGoingVertices(v),
                        (x) -> x.Location > v.Location
                ));
                var check = Utilities.anyTrue(inVs,
                        (x) -> wm.get(x).equals("V")
                );
                if (check)
                {
                    seenAction.apply();
                    v.isAdditionalProcessedVertex = true;
                    return;
                }
            }
        }

    }

    public static HashSet<WordVertex> recursiveVertices(Graph<WordVertex> tree, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var res = new HashSet<WordVertex>();
        var wm = getWordMeaningType(tree);
        var vs = Utilities.makeArrayList(tree.vertexList());
        Utilities.topologicalSort(vs,
                (x, y) ->
                {
                    var path = tree.findPath(x, y);
                    if (path != null)
                        return -1;
                    path = tree.findPath(y, x);
                    if (path != null)
                        return 1;
                    return 0;
                }
        );
        for (var v : vs)
        {
            if (tree.vertexOutDegree(v) == 0)
                continue;
            var inVs = tree.vertexInComponent(v);
            if (Utilities.anyTrue(processedGroups, (x) -> Utilities.containsAll(x, inVs)))
                continue;
            if (tree.vertexOutDegree(v) == 0 || !Utilities.getFirstElement(tree.outGoingVertices(v)).Type.startsWith("N"))
                if (wm.get(v).equals("N"))
                    if (Utilities.anyTrue(inVs, (x) -> isInNounCompound(x)) && Utilities.allTrue(inVs, (x) ->
                    {
                        /*x.Type.equals("R") || isInNounCompound(x)*/
                        return !x.Type.equals("V");
                    }))
                    {
                        res.add(v);
                        return res;
                    }
            if (v.isMarked)
            {
                res.add(v);
                return res;
            }
        }
        return res;
    }

    public static HashMap<WordVertex, String> getWordMeaningType(Graph<WordVertex> tree)
    {
        var vs = Utilities.makeArrayList(tree.vertexList());
        Utilities.topologicalSort(vs,
                (x, y) ->
                {
                    var path = tree.findPath(x, y);
                    if (path != null)
                        return -1;
                    path = tree.findPath(y, x);
                    if (path != null)
                        return 1;
                    return 0;
                }
        );
        UnaryFunction<WordVertex, Boolean> isNoun = (x) ->
        {
            return x.Type.equals("P") || x.Type.startsWith("N");
        };
        var res = new HashMap<WordVertex, String>();
        for (var v : vs)
        {
            if (v.Type.equals("A"))
            {
                var inVs = tree.inGoingVertices(v);
                /*if (Utilities.allTrue(inVs, (x) -> x.Location < v.Location))*/
                if (Utilities.anyTrue(inVs, (x) -> x.Location < v.Location && res.get(x).equals("N")))
                {
                    res.put(v, "N");
                    continue;
                }
            }
            var type = v.Type;
            if (!isNoun.apply(v) && !type.equals("V"))
            {
                res.put(v, type);
                continue;
            }
            if (isNoun.apply(v))
            {
                res.put(v, "N");
                continue;
            }
            if (type.equals("V"))
            {
                var inVs = tree.inGoingVertices(v);
                if (inVs.size() == 0)
                    res.put(v, "V");
                else if (Utilities.anyTrue(inVs, (x) -> res.get(x).equals("N") && x.Location < v.Location))
                    res.put(v, "N");
                else res.put(v, "V");
            }
        }
        return res;
    }

    public static boolean isInNounCompound(WordVertex v)
    {
        var type = v.Type;
        return type.startsWith("N") || type.equals("A") || type.equals("L") || type.equals("M") || type.equals("P");
    }

    public static boolean isInNounCompound(Graph<WordVertex> tree, WordVertex v)
    {
        if (v.Word.equals("của") && v.Type.equals("E"))
            return true;
        if (v.Word.equals("ấy") && v.Type.equals("P"))
            return true;
        var type = v.Type;
        if (type.startsWith("N") || type.equals("L") || type.equals("M") || type.equals("P"))
            return true;
        if (type.equals("A"))
        {
            var inVs = tree.inGoingVertices(v);
            /*if (Utilities.allTrue(inVs, (x) -> x.Location < v.Location))
            {*/
            if (Utilities.anyTrue(inVs, (x) -> x.Location < v.Location && x.Type.startsWith("N")))
                return true;
            /*}*/
            var outVs = tree.outGoingVertices(v);
            if (outVs.size() == 0)
                return false;
            else
            {
                var outV = Utilities.getFirstElement(outVs);
                if (outV.Location < v.Location && outV.Type.equals("V"))
                    return false;
                else return true;
            }
        }
        return false;
    }

    public static boolean isWaitingToCompleteNoun(Graph<WordVertex> tree, WordVertex v)
    {
        var wm = getWordMeaningType(tree);
        if (!wm.get(v).equals("N"))
            return false;
        if (!v.Type.equals("V"))
            return false;
        var inVs = Utilities.select(tree.inGoingVertices(v),
                (x) -> x.Location > v.Location
        );
        if (Utilities.anyTrue(inVs, (x) -> wm.get(x).equals("N")))
            return false;
        else return true;
    }

    public static void nounCompoundModifyTree(Graph<WordVertex> g, Graph<WordVertex> tree, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var vs = Utilities.makeArrayList(tree.vertexList());
        var wm = getWordMeaningType(tree);
        Utilities.topologicalSort(vs,
                (x, y) ->
                {
                    var path = tree.findPath(x, y);
                    if (path != null)
                        return -1;
                    path = tree.findPath(y, x);
                    if (path != null)
                        return 1;
                    return 0;
                }
        );
        final UnaryFunction<WordVertex, Boolean> splitByAction = (x) ->
        {
            var aux = tree.vertexInComponent(x);
            return !(Utilities.anyTrue(aux, (y) -> isInNounCompound(tree, y)) && Utilities.allTrue(aux,
                    (y) -> isInNounCompound(tree, y) || y.Type.equals("R")
            ));
        };
        var originGraph = (Graph<WordVertex>) tree.getGraphProperty("origin graph");
        var root = getRoot(tree);
        UnaryFunction<WordVertex, Boolean> isStrongCompoundNound = (x) ->
        {
            var inVx = tree.vertexInComponent(x);
            return Utilities.allTrue(inVx,
                    (y) -> !y.Type.equals("V")
            );
        };
        var stopped = new AtomicReference<Boolean>();
        stopped.set(false);
        BinaryAction<WordVertex, ArrayList<ArrayList<WordVertex>>> splitsAction = (v, splits) ->
        {
            for (var split : splits)
            {
                if (split.size() <= 1)
                    continue;
                var firstEle = split.get(0);
                var loc = v.Location < firstEle.Location ? "right" : "left";
                if (loc.equals("right") && v.Type.equals("V") && split.size() == 2 && !isWaitingToCompleteNoun(tree, firstEle))
                {
                    if (!Utilities.allTrue(split, (x) -> isStrongCompoundNound.apply(x)))
                        if (Utilities.count(tree.inGoingVertices(v), (x) -> x.Location > v.Location) == 2)
                            continue;
                }
                if (firstEle.Location < root.Location)
                {
                    if (!checkUnion(tree, split, processedGroups))
                        continue;
                    for (var i = 1; i <= split.size() - 1; i++)
                    {
                        var iEle = split.get(i);
                        tree.deleteEdge(iEle, v);
                        tree.addEdge(iEle, firstEle);
                    }
                    var inVs = tree.vertexInComponent(firstEle);
                    Utilities.map((x) ->
                    {
                        x.resetAdditionalProperties();
                    }, inVs);
                    Utilities.map((x) ->
                    {
                        x.isProcessedVertex = true;
                    }, split);
                    firstEle.isMarked = true;
                    stopped.set(true);
                    return;
                } else
                {
                    var auxg = new Graph<WordVertex>();
                    for (var i = 0; i <= split.size() - 2; i++)
                    {
                        var iEle = split.get(i);
                        var nextIEle = split.get(i + 1);
                        if (isStrongCompoundNound.apply(iEle) && isStrongCompoundNound.apply(nextIEle) || isWaitingToCompleteNoun(tree, iEle))
                        {
                            auxg.addVertex(iEle);
                            auxg.addVertex(nextIEle);
                            auxg.addEdge(iEle, nextIEle);
                        }
                    }
                    var auxgComposes = auxg.weaklyConnectedComponents();
                    var splitSubgraph = originGraph.subgraph(split);
                    for (var auxgCompos : auxgComposes)
                    {
                        if (auxgCompos.size() <= 1)
                            continue;
                        var subg = g.subgraph(auxgCompos);
                        for (var ed : subg.edgeList())
                        {
                            splitSubgraph.addEdge(ed);
                            splitSubgraph.setEdgeWeight(ed, g.getEdgeWeight(ed));
                        }
                    }
                    var compos = splitSubgraph.weaklyConnectedComponents();
                    for (var comp : compos)
                    {
                        if (comp.size() <= 1)
                            continue;
                        var compar = Utilities.makeArrayList(comp);
                        Utilities.sortBy(compar, (x) -> x.Location);
                        if (!checkUnion(tree, compar, processedGroups))
                            continue;
                        var fE = compar.get(0);
                        for (var i = 1; i <= compar.size() - 1; i++)
                        {
                            var iEle = compar.get(i);
                            tree.deleteEdge(iEle, v);
                            tree.addEdge(iEle, fE);
                        }
                        var inVs = tree.vertexInComponent(fE);
                        Utilities.map((x) ->
                        {
                            x.resetAdditionalProperties();
                        }, inVs);
                        fE.isMarked = true;
                        Utilities.map((x) ->
                        {
                            x.isProcessedVertex = true;
                        }, compar);
                        stopped.set(true);
                        return;
                    }
                }

            }
        };
        for (var v : vs)
        {
            var inCompoV = tree.vertexInComponent(v);
            if (Utilities.anyTrue(processedGroups, (x) -> Utilities.containsAll(x, inCompoV)))
                continue;
            if (v.Type.startsWith("N"))
                continue;
            var inVs = tree.inGoingVertices(v);
            var leftInVs = Utilities.select(inVs,
                    (x) -> x.Location < v.Location
            );
            Utilities.sortBy(leftInVs, (x) -> x.Location);
            var leftSplits = Utilities.splitBy(leftInVs, (x) -> splitByAction.apply(x) && !wm.get(x).equals("N"));
            splitsAction.apply(v, leftSplits);
            if (stopped.get())
                break;
            var rightVs = Utilities.select(inVs,
                    (x) -> x.Location > v.Location
            );
            Utilities.sortBy(rightVs, (x) -> x.Location);
            var rightSplits = Utilities.splitBy(rightVs, (x) -> !v.Type.equals("V") ? splitByAction.apply(x) && !wm.get(x).equals("N")
                    : splitByAction.apply(x) && !isWaitingToCompleteNoun(tree, x));
            splitsAction.apply(v, rightSplits);
            if (stopped.get())
                break;
        }
    }

    final static ArrayList<ArrayList<String>> specialPronouns = (ArrayList<ArrayList<String>>) Utilities.toArrayList(new String[][]{
            {"ấy", "P"}, {"đó", "P"}, {"cả", "P"}, {"kia",
            "P"}, {"ta", "P"}, {"nào", "P"}, {"này", "P"}, {"từng",
            "P"}, {"tự", "P"}, {"nay", "P"}
    });

    public static boolean isVerbComplete(Graph<WordVertex> tree, HashMap<WordVertex, String> wm, WordVertex v)
    {
        if (!wm.get(v).equals("V"))
            return true;
        var runningV = v;
        var vs = tree.vertexList();
        var wrappedRunningV = new AtomicReference<WordVertex>();
        wrappedRunningV.set(runningV);
        while (true)
        {
            var outVs = tree.outGoingVertices(runningV);
            if (outVs.size() == 0)
                return true;
            var outV = Utilities.getFirstElement(outVs);
            if (outV.Location > runningV.Location)
                return false;
            wrappedRunningV.set(runningV);
            if (runningV.Type.equals("V") && outV.Type.equals("V"))
                if (Utilities.anyTrue(vs, (x) -> outV.Location < x.Location && x.Location < wrappedRunningV.get().Location && (!wm.get(x).equals("N") && !wm.get(x).equals("V") /*&& !x.Type.equals("X")*/)))
                    return false;
            if (wm.get(outV).equals("N"))
                return true;
            if (wm.get(outV).equals("V"))
            {
                runningV = outV;
                continue;
            } else return false;
        }
    }

    public static boolean checkUnion(Graph<WordVertex> tree, Collection<WordVertex> vs, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var union = new HashSet<WordVertex>();
        for (var v : vs)
            union.addAll(tree.vertexInComponent(v));
        return !Utilities.anyTrue(processedGroups,
                (x) -> Utilities.containsAll(x, union)
        );
    }

    public static void lMModifyTree(Graph<WordVertex> tree, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var consideredTypes = new CustomHashSet<>(new String[]{"L", "M"});
        var wm = getWordMeaningType(tree);
        TernaryFunction<ArrayList<WordVertex>, WordVertex, WordVertex, Boolean> func = (inVs, m, above) ->
        {
            Utilities.sortBy(inVs, (x) -> x.Location);
            var firstNPos = Utilities.firstPosition(inVs, (x) ->
            {
                return x.Location > m.Location && wm.get(x).equals("N");
            });
            if (firstNPos == null)
                return false;
            var nPosEle = inVs.get(firstNPos);
            var mPos = Utilities.firstPosition(inVs, (x) -> x.equals(m));
            var range = Utilities.part(inVs, mPos, firstNPos);
            if (checkUnion(tree, range, processedGroups))
            {
                for (var i = mPos; i <= firstNPos - 1; i++)
                {
                    var iEle = inVs.get(i);
                    tree.deleteEdge(iEle, above);
                    tree.addEdge(iEle, nPosEle);
                }
                var aux = tree.vertexInComponent(nPosEle);
                Utilities.map((WordVertex x) ->
                {
                    x.resetAdditionalProperties();
                }, aux);
                nPosEle.isMarked = true;
                for (var i = mPos + 1; i <= firstNPos; i++)
                    inVs.get(i).isProcessedVertex = true;
                return true;
            }
            return false;
        };
        for (var v : tree.vertexList())
        {
            if (consideredTypes.contains(v.Type))
                if (tree.vertexInDegree(v) == 0)
                {
                    if (tree.vertexOutDegree(v) == 0)
                        continue;
                    var outV = Utilities.getFirstElement(tree.outGoingVertices(v));
                    if (!outV.Type.startsWith("N"))
                    {
                        ArrayList<WordVertex> inVs;
                        if (v.Location < outV.Location)
                        {
                            inVs = Utilities.select(tree.inGoingVertices(outV),
                                    (x) -> x.Location < outV.Location
                            );
                        } else
                        {
                            inVs = Utilities.select(tree.inGoingVertices(outV),
                                    (x) -> x.Location > outV.Location
                            );
                        }
                        var res = func.apply(inVs, v, outV);
                        if (res)
                            return;
                    }
                }
        }
    }

    public static void nonCompleteVerbModifyTree(Graph<WordVertex> tree, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var wm = getWordMeaningType(tree);
        var coors = assignTreeCoordinate(tree);
        BinaryFunction<WordVertex, WordVertex, Number> treeOrder = (x, y) ->
        {
            var path = tree.findPath(x, y);
            if (path != null)
                return -1;
            path = tree.findPath(y, x);
            if (path != null)
                return 1;
            return 0;
        };
        for (var v : tree.vertexList())
        {
            if (wm.get(v).equals("V") && !isVerbComplete(tree, wm, v))
            {
                var outVs = tree.outGoingVertices(v);
                if (outVs.size() == 0)
                    continue;
                var outV = Utilities.getFirstElement(outVs);
                var selectedVs = Utilities.select(tree.vertexList(),
                        (x) ->
                        {
                            var check0 = outV.Location < x.Location && x.Location < v.Location;
                            if (!check0)
                                return false;
                            var check1 = Utilities.lexicographicOrder(coors.get(x), coors.get(v), (u, z) -> u - z) < 0;
                            if (!check1)
                                return false;
                            var inVs = tree.vertexInComponent(x);
                            return Utilities.allTrue(inVs,
                                    (y) -> isInNounCompound(tree, y)
                            );
                        }
                );
                if (selectedVs.size() == 0)
                    continue;
                var maximalVs = Utilities.maximals(selectedVs, treeOrder);
                var maxV = Utilities.getFirstElement(Utilities.maximals(maximalVs,
                        (x, y) -> Utilities.lexicographicOrder(coors.get(x), coors.get(y), (u, z) -> u - z)
                ));
                var interval = Utilities.select(tree.vertexList(),
                        (x) ->
                        {
                            var check0 = Utilities.lexicographicOrder(coors.get(maxV), coors.get(x), (u, z) -> u - z) <= 0;
                            var check1 = Utilities.lexicographicOrder(coors.get(x), coors.get(v), (u, z) -> u - z) <= 0;
                            return check0 && check1;
                        }
                );
                var intervalMaximals = Utilities.makeArrayList(Utilities.maximals(interval, treeOrder));
                Utilities.quickSort(intervalMaximals,
                        (x, y) -> Utilities.lexicographicOrder(coors.get(x), coors.get(y), (z, t) -> z - t)
                );
                if (checkUnion(tree, intervalMaximals, processedGroups))
                {
                    for (var i = 1; i <= intervalMaximals.size() - 1; i++)
                    {
                        var w = intervalMaximals.get(i);
                        var outW = Utilities.getFirstElement(tree.outGoingVertices(w));
                        tree.deleteEdge(w, outW);
                        tree.addEdge(w, maxV);
                    }
                    var inVs = tree.vertexInComponent(maxV);
                    Utilities.map((WordVertex x) ->
                    {
                        x.resetAdditionalProperties();
                    }, inVs);
                    maxV.isMarked = true;
                    for (var w : intervalMaximals)
                        w.isProcessedVertex = true;
                    return;
                }
            }
        }
    }

    public static void nounVerbModifyTree(Graph<WordVertex> tree, HashSet<HashSet<WordVertex>> processedGroups)
    {
        var wm = getWordMeaningType(tree);
        UnaryFunction<WordVertex, Boolean> isNoun = (x) ->
        {
            return wm.get(x).equals("N");
        };
        var stopped = new AtomicReference<Boolean>();
        stopped.set(false);
        BinaryAction<WordVertex, ArrayList<WordVertex>> processVs = (v, inVs) ->
        {
            Utilities.sortBy(inVs, (x) -> x.Location);
            var i = 0;
            while (i <= inVs.size() - 1)
            {
                var iV = inVs.get(i);
                if (!isNoun.apply(iV))
                {
                    i++;
                    continue;
                }
                var firstVPos = Utilities.firstPosition(inVs,
                        (x) -> (x.Location > iV.Location) && wm.get(x).equals("V") && !isVerbComplete(tree, wm, x)
                );
                if (firstVPos == null)
                    break;
                var firstVPosEle = inVs.get(firstVPos);
                var betweens = Utilities.part(inVs, i + 1, firstVPos - 1);
                var lastNPos = Utilities.lastPosition(betweens, isNoun);
                if (lastNPos == null)
                    lastNPos = -1;
                var subBetweens0 = Utilities.part(betweens, 0, lastNPos);
                if (!Utilities.allTrue(subBetweens0, isNoun))
                {
                    i++;
                    continue;
                }
                var subBetweens1 = Utilities.part(betweens, lastNPos + 1, betweens.size() - 1);
                if (Utilities.allTrue(subBetweens1,
                        (x) ->
                        {
                            var aux = wm.get(x);
                            return aux.equals("R") || aux.equals("C");
                        }
                ))
                {
                    var unionVs = Utilities.part(inVs, i, firstVPos);
                    if (!checkUnion(tree, unionVs, processedGroups))
                    {
                        i++;
                        continue;
                    }
                    for (var j = i; j <= firstVPos.intValue() - 1; j++)
                    {
                        tree.deleteEdge(inVs.get(j), v);
                        tree.addEdge(inVs.get(j), firstVPosEle);
                    }
                    {
                        var aux = tree.vertexInComponent(firstVPosEle);
                        Utilities.map((WordVertex y) ->
                        {
                            y.resetAdditionalProperties();
                        }, aux);
                    }
                    firstVPosEle.isMarked = true;
                    firstVPosEle.isProcessedVertex = true;
                    for (var j = i; j <= firstVPos.intValue() - 1; j++)
                        inVs.get(j).isProcessedVertex = true;
//                    if (tree.vertexOutDegree(firstVPosEle) > 0)
//                    {
//                        var auxV = Utilities.getFirstElement(tree.outGoingVertices(firstVPosEle));
//                        if (auxV.Type.equals("E"))
//                        {
//                            if (Utilities.count(inVs, (x) ->
//                            {
//                                return x.isProcessedVertex && !x.Type.equals("V");
//                            }) > 0)
//                            {
//                                Utilities.map((WordVertex x) ->
//                                {
//                                    if (x.isProcessedVertex && x.Type.equals("V"))
//                                        x.isProcessedVertex = false;
//                                }, inVs);
//                            }
//                        }
//                    }
                    i = firstVPos + 1;
                    stopped.set(true);
                    return;
                } else
                {
                    i++;
                    continue;
                }
            }
        };
        for (var v : tree.vertexList())
        {
            var inCompoV = tree.vertexInComponent(v);
            if (Utilities.anyTrue(processedGroups, (x) -> Utilities.containsAll(x, inCompoV)))
                continue;
            var inVs = Utilities.select(tree.inGoingVertices(v),
                    (x) -> x.Location < v.Location
            );
            processVs.apply(v, inVs);
            if (stopped.get())
                break;
            inVs = Utilities.select(tree.inGoingVertices(v),
                    (x) -> x.Location > v.Location
            );
            processVs.apply(v, inVs);
            if (stopped.get())
                break;
        }
    }

    public static HashMap<EdgeVertex, Double> EdgePR = null;
    public static HashMap<ArrayList<String>, Double> VertexPR = null;

    public static Graph<WordVertex> decideParser(ArrayList<String> sentence)
    {
        return decideParser(sentence, false);
    }

    public static Graph<WordVertex> decideParser(ArrayList<String> sentence, boolean showTree)
    {
        var g = makeDependenceGraph(EdgePR, VertexPR, sentence);
        return decideParser(g, showTree);
    }

//    public static Graph<WordVertex> decideParser(Graph<WordVertex> g)
//    {
//        return decideParser(g, false);
//    }

    public static Graph<WordVertex> decideParser(Graph<WordVertex> g, boolean showTree)
    {
        var opts = new HashMap<String, Object>();
        opts.put("cycleDetection", false);
        var typeSet = new ArrayList<HashSet<WordVertex>>();
        var storedTrees = new ArrayList<Graph<WordVertex>>();
        var runningTreeWrapped = new AtomicReference<Graph<WordVertex>>();
        runningTreeWrapped.set(preDecideParser(g));
        typeSet.add(Utilities.makeHashSet(runningTreeWrapped.get().vertexList()));
        storedTrees.add(runningTreeWrapped.get());
        if (showTree)
        {
            Utilities.executeMathematicaCode("Echo[DrawParser[%0]]", runningTreeWrapped.get());
            Utilities.executeMathematicaCode("Echo[%0@toString[]]", countErrors(runningTreeWrapped.get()));
        }
        while (true)
        {
            var types = adjustTypes(g, runningTreeWrapped.get());
            if (types == null)
                return runningTreeWrapped.get();
            if (typeSet.contains(types))
            {
                var pos = Utilities.firstPosition(typeSet,
                        (x) -> x.equals(types)
                );
                var consideredTrees = Utilities.part(storedTrees, pos, storedTrees.size() - 1);
//                for (var shownTree : consideredTrees)
//                    Utilities.executeMathematicaCode("Echo@DrawParser@%0", shownTree);
                var mins = Utilities.minimals(consideredTrees,
                        (tree0, tree1) ->
                        {
                            var errors0 = countErrors(tree0);
                            var errors1 = countErrors(tree1);
                            var ec = errorCompare(errors0, errors1);
                            if (ec != 0)
                                return ec;
                            else return toRootDistanceVariance(tree0) - toRootDistanceVariance(tree1);
                        }
                );
                if (showTree)
                {
                    Utilities.executeMathematicaCode("Echo[showing mins]");
                    for (var minTree : mins)
                        Utilities.executeMathematicaCode("Echo[DrawParser[%0]]", minTree);
                }
                return Utilities.getFirstElement(mins);
            }
            var subg = g.subgraph(types);
            var newTree = strongRecursiveMaxTree(subg, opts);
            runningTreeWrapped.set(newTree);
            typeSet.add(types);
            storedTrees.add(newTree);
            if (showTree)
            {
                Utilities.executeMathematicaCode("Echo[DrawParser[%0]]", runningTreeWrapped.get());
                Utilities.executeMathematicaCode("Echo[%0@toString[]]", countErrors(runningTreeWrapped.get()));
            }
        }
    }

    public static Graph<WordVertex> preDecideParser(Graph<WordVertex> g)
    {
        var types = decideVertexTypes(g, true);
        var subG = g.subgraph(types);
        var opts = new HashMap<String, Object>();
        opts.put("cycleDetection", false);
        return strongRecursiveMaxTree(/*g*/subG, opts);
    }

    public static Graph<WordVertex> strongRecursiveMaxTree(Graph<WordVertex> g, HashMap<String, Object> opts)
    {
        var processedGroups = new HashSet<HashSet<WordVertex>>();
        return strongRecursiveMaxTree(g, processedGroups, opts, 0);
    }

    private static void localDeleteEdges(Graph<WordVertex> g, Collection<WordVertex> vs)
    {
        var eds = g.edgeList();
        for (var ed : eds)
            if (vs.contains(ed.get(0)) && vs.contains(ed.get(1)))
                g.deleteEdge(ed);
    }

    public static Graph<WordVertex> strongRecursiveMaxTree(Graph<WordVertex> g,
                                                           HashSet<HashSet<WordVertex>> processedGroups,
                                                           HashMap<String, Object> opts, int recursiveLevel)
    {
        UnaryFunction<Graph<WordVertex>, Graph<WordVertex>> makeTreeFiner = (tree) ->
        {
            var copiedOpts = (HashMap<String, Object>) opts.clone();
            copiedOpts.put("startingEdges", tree.edgeList());
            var root = getRoot(tree);
            return maximumSpanningTree(g, root, copiedOpts);
        };
        Graph<WordVertex> maxTree = recursiveMaxTree(g, opts);
        while (true)
        {
            var meetQ = false;
            var storedMaxTree = (Graph<WordVertex>) maxTree.clone();
            Utilities.map((WordVertex x) ->
            {
                x.resetAdditionalProperties();
            }, g.vertexList());
            UnaryFunction<WordVertex, Boolean> selectingAction = (x) ->
            {
                var inXs = maxTree.vertexInComponent(x);
                return !Utilities.anyTrue(processedGroups,
                        (y) -> Utilities.containsAll(y, inXs)
                );
            };
            var actions = new NullAction[]{
                    () ->
                    {
                    },
                    () ->
                    {
                        sentenceModifyTree(maxTree, processedGroups);
                    }
            };
            var status = "None";
            HashSet<WordVertex> rVs = new HashSet<>();
            for (var i = 0; i <= actions.length - 1; i++)
            {
                switch (i)
                {
                    case 0:
                        status = "None";
                        break;
                    case 1:
                        status = "sentenceModifyTree";
                        break;
                    case 2:
                        status = "nonCompleteVerbModifyTree";
                        break;
                    case 3:
                        status = "nounCompoundModifyTree";
                        break;
                }
                var action = actions[i];
                action.apply();
                rVs = Utilities.makeHashSet(Utilities.select(recursiveVertices(maxTree, processedGroups),
                        selectingAction
                ));
                if (rVs.size() != 0)
                    break;
            }
            if (rVs.size() == 0)
                break;
            var minimalVertices = Utilities.minimals(Utilities.select(rVs,
                            (z) ->
                            {
                                var inVsZ = maxTree.vertexInComponent(z);
                                return !Utilities.anyTrue(processedGroups, (u) -> Utilities.containsAll(u, inVsZ));
                            }
                    ),
                    (x, y) ->
                    {
                        if (x.equals(y))
                            return 0;
                        var path = maxTree.findPath(x, y);
                        if (path != null)
                            return -1;
                        path = maxTree.findPath(y, x);
                        if (path != null)
                            return 1;
                        return 0;
                    }
            );
            for (var v : minimalVertices)
            {
                var outV = Utilities.getFirstElement(maxTree.outGoingVertices(v));
                var inVs = maxTree.vertexInComponent(v);
                Graph<WordVertex> subG;
                subG = g.subgraph(inVs);
                var maximalProcessedGroups = Utilities.maximals(
                        Utilities.select(processedGroups,
                                (group) -> Utilities.containsAll(inVs, group)
                        ),
                        (group0, group1) ->
                        {
                            if (group0.equals(group1))
                                return 0;
                            if (Utilities.containsAll(group0, group1))
                                return 1;
                            if (Utilities.containsAll(group1, group0))
                                return -1;
                            return 0;
                        }
                );
                for (var group : maximalProcessedGroups)
                {
                    localDeleteEdges(subG, group);
                    var groupG = storedMaxTree.subgraph(group);
                    for (var ed : groupG.edgeList())
                    {
                        subG.addEdge(ed);
                        subG.setEdgeWeight(ed, g.getEdgeWeight(ed));
                    }
                    subG.deleteEdges(
                            Utilities.select(subG.edgeList(),
                                    (ed) ->
                                    {
                                        var v0 = ed.get(0);
                                        var v1 = ed.get(1);
                                        if (!groupG.containsVertex(v0))
                                            return false;
                                        if (groupG.vertexOutDegree(v0) == 0)
                                            return false;
                                        var outV0s = groupG.outGoingVertices(v0);
                                        var outV0 = Utilities.getFirstElement(outV0s);
                                        var auxEd = new CustomArrayList<WordVertex>(new WordVertex[]{v0, outV0});
                                        return !groupG.containsVertex(v1) && !isErrorEdge(groupG, auxEd) /*isTrustedEdge(auxEd)*/;
                                    }
                            )
                    );
                }
                if (subG.weaklyConnectedComponents().size() > 1)
                {
                    maxTree.deleteEdges(maxTree.edgeList());
                    maxTree.addEdges(storedMaxTree.edgeList());
                    processedGroups.add(inVs);
                    break;
                }
                var subRes = strongRecursiveMaxTree(subG, processedGroups, opts, recursiveLevel + 1);
                processedGroups.add(inVs);
                meetQ = true;
                var subRoot = Utilities.firstCase(subRes.vertexList(),
                        (x) -> subRes.vertexOutDegree(x) == 0
                );
                var removedEds = Utilities.select(maxTree.subgraph(inVs).edgeList()/*g.edgeList()*/,
                        (ed) ->
                        {
                            var v0 = ed.get(0);
                            var v1 = ed.get(1);
                            return inVs.contains(v0) && inVs.contains(v1);
                        }
                );
                removedEds.add(new CustomArrayList<WordVertex>(new WordVertex[]{v, outV}));
                if (v.Location < outV.Location)
                {
                    var copiedMaxTree = (Graph<WordVertex>) maxTree.clone();
                    copiedMaxTree.deleteEdges(removedEds);
                    copiedMaxTree.addEdges(subRes.edgeList());
                    copiedMaxTree.addEdge(new CustomArrayList<WordVertex>(new WordVertex[]{subRoot, outV}));
                    if (errorCompare(countErrors(copiedMaxTree), countErrors(storedMaxTree)) <= 0)
                    {
                        maxTree.deleteEdges(removedEds);
                        maxTree.addEdges(subRes.edgeList());
                        maxTree.addEdge(new CustomArrayList<WordVertex>(new WordVertex[]{subRoot, outV}));
//                        break;
                    } else
                    {
                        maxTree.deleteEdges(maxTree.edgeList());
                        maxTree.addEdges(storedMaxTree.edgeList());
//                        break;
                    }
                } else
                {
                    maxTree.deleteEdges(removedEds);
                    maxTree.addEdges(subRes.edgeList());
                    maxTree.addEdge(new CustomArrayList<WordVertex>(new WordVertex[]{subRoot, outV}));
//                    break;
                }
                var showTrees = false;
                if (opts.containsKey("Show Trees"))
                    showTrees = (boolean) opts.get("Show Trees");
                var shownLevel = 0;
                if (opts.containsKey("Shown Recursive Level"))
                    shownLevel = (int) opts.get("Shown Recursive Level");
                if (showTrees && recursiveLevel == shownLevel)
                {
                    /*Utilities.executeMathematicaCode("If[!JavaObjectQ@MyObject,MyObject=%0]",storedMaxTree);*/
                    Utilities.executeMathematicaCode("Echo[SmartToString@%0]", v);
                    Utilities.executeMathematicaCode("Echo[%0@toString[]]", status);
                    Utilities.executeMathematicaCode("Echo[DrawParser@%0]", storedMaxTree);
                    Utilities.executeMathematicaCode("Echo[DrawParser@%0]", maxTree);
//                    Utilities.executeMathematicaCode("Echo[ConvertToMGraph[%0,VertexLabels->{x_:>x@toString[]}]]", maxTree);
                    Utilities.executeMathematicaCode("Echo[ConvertToMGraph[%0,VertexLabels->{x_:>x@toString[]}]]", subG);
                    Utilities.executeMathematicaCode("Echo[DrawParser@%0]", subRes);
                }
            }
        }
        /*var finerTree = makeTreeFiner.apply(maxTree);*/
        maxTree.setGraphProperty("processed groups", processedGroups);
        return maxTree;
    }

    public static double errorCompare(HashMap<String, Object> errors0,
                                      HashMap<String, Object> errors1)
    {
        var errorImportance = getErrorAppearanceStatics();
//        var size = Parsers.size();
//        var sum0 = 0d;
//        var sum1 = 0d;
//        for (var name : errorImportance.keySet())
//        {
//            var size0 = ((Collection) errors0.get(name)).size();
//            var size1 = ((Collection) errors1.get(name)).size();
//            var diff0 = ((double) errorImportance.get(name)) / size - size0;
//            var diff1 = ((double) errorImportance.get(name)) / size - size1;
//            sum0 = sum0 + diff0 * diff0;
//            sum1 = sum1 + diff1 * diff1;
//        }
//        if (sum0 == sum1)
//            return 0;
//        else return sum0 < sum1 ? -1 : 1;
        var propertyNames = Utilities.makeArrayList(errorImportance.keySet());
        Utilities.sortBy(propertyNames, (x) -> errorImportance.get(x));
        var values0 = new ArrayList<Double>();
        var values1 = new ArrayList<Double>();
        for (var erType : propertyNames)
        {
            if (errors0.containsKey(erType))
                values0.add(Double.valueOf(((HashSet) errors0.get(erType)).size()));
            else values0.add(0d);

            if (errors1.containsKey(erType))
                values1.add(Double.valueOf(((HashSet) errors1.get(erType)).size()));
            else values1.add(0d);
        }
        var order = Utilities.lexicographicOrder(values0, values1, (x, y) -> x - y);
        if (order != 0)
            return order;
        return 0;
    }

    public static int treeBalance(Graph<WordVertex> tree)
    {
        var root = getRoot(tree);
        var left = Utilities.count(tree.vertexList(), (x) -> x.Location < root.Location);
        var right = Utilities.count(tree.vertexList(), (x) -> x.Location > root.Location);
        return Math.abs(left - right);
    }

    public static int edgeDistanceCompare(Graph<WordVertex> tree0, Graph<WordVertex> tree1)
    {
        var distances0 = Utilities.map((ArrayList<WordVertex> ed) -> Math.abs(ed.get(0).Location - ed.get(1).Location),
                tree0.edgeList()
        );
        var distances1 = Utilities.map((ArrayList<WordVertex> ed) -> Math.abs(ed.get(0).Location - ed.get(1).Location),
                tree1.edgeList()
        );
        while (true)
        {
            try
            {
                var ele = Utilities.firstCase(distances0,
                        (x) -> distances1.contains(x)
                );
                distances0.remove(ele);
                distances1.remove(ele);
            } catch (Exception e)
            {
                if (distances0.size() == 0)
                    break;
                else
                {
                    /*var max0 = Utilities.max(distances0).intValue();
                    var max1 = Utilities.max(distances1).intValue();*/
                    /*if (max0 != max1)
                        return max0 < max1 ? -1 : 1;*/
                    var mean0 = Utilities.mean(distances0);
                    var mean1 = Utilities.mean(distances1);
                    if (mean0 != mean1)
                        return mean0 < mean1 ? -1 : 1;
                }
            }
        }
        return 0;
    }

    public static HashSet<WordVertex> isolatedVertices(Graph<WordVertex> g)
    {
        return Utilities.makeHashSet(
                Utilities.select(g.vertexList(), x -> g.vertexInDegree(x) == 0 && g.vertexOutDegree(x) == 0)
        );
    }

    public static double errorTreeCompare(Graph<WordVertex> tree0, Graph<WordVertex> tree1)
    {
        return errorTreeCompare(tree0, tree1, false);
    }

    public static double errorTreeCompare(Graph<WordVertex> tree0, Graph<WordVertex> tree1, boolean ignoreErrors)
    {
        var isoVs0 = isolatedVertices(tree0);
        var isoVs1 = isolatedVertices(tree1);
        var auxTree0 = tree0.clone();
        var auxTree1 = tree1.clone();
        Utilities.map(
                tree ->
                {
                    if (tree instanceof Parser)
                        tree.deleteEdges(((Parser) tree).MeaningSupplementEdges);
                }, new Graph[]{auxTree0, auxTree1}
        );

        auxTree0.deleteVertices(isoVs0);
        auxTree1.deleteVertices(isoVs1);
        var violations0 = countViolations(auxTree0);
        var violations1 = countViolations(auxTree1);
        if (violations0 != violations1)
            return violations0 < violations1 ? -1 : 1;
        if (!ignoreErrors)
        {
            var errors0 = countErrors(auxTree0);
            var errors1 = countErrors(auxTree1);
            var res = errorCompare(errors0, errors1);
            if (res != 0)
                return res;
        }
        var weight0 = getTreeWeight(auxTree0);
        var weight1 = getTreeWeight(auxTree1);
        return weight0 < weight1 ? 1 : (weight0 > weight1 ? -1 : 0);
    }

    private static WordVertex getRoot(Graph<WordVertex> tree)
    {
        return Utilities.firstCase(tree.vertexList(), (x) -> tree.vertexOutDegree(x) == 0);
    }

    public static void normalizeProcessingNouns(ArrayList<WordVertex> processedNs)
    {
        var wNs = (ArrayList<WordVertex>) (Object) Utilities.reverse(processedNs);
        var indexf = new HashMap<WordVertex, Integer>();
        for (var i = 0; i <= wNs.size() - 1; i++)
            indexf.put(wNs.get(i), i);
        var relG = Graph.relationGraph(wNs,
                (x, y) ->
                {
                    var check0 = x.Type.equals("P") || x.Type.startsWith("N");
                    var check1 = y.Type.equals("P") || y.Type.startsWith("N");
                    return check0 && check1 && Math.abs(indexf.get(x) - indexf.get(y)) == 1 &&
                            Math.abs(x.Location - y.Location) == 1;
                }
        );
        var composes = Utilities.makeArrayList(relG.weaklyConnectedComponents());
        var compoIndexf = new HashMap<WordVertex, Integer>();
        for (var i = 0; i <= composes.size() - 1; i++)
        {
            var compos = composes.get(i);
            for (var v : compos)
                compoIndexf.put(v, i);
        }
        /*System.out.println("wNs " + wNs);*/
        wNs = Utilities.deleteDuplicates(wNs, (x, y) -> compoIndexf.get(x).equals(compoIndexf.get(y)));
        wNs = (ArrayList<WordVertex>) (Object) Utilities.reverse(wNs);
        processedNs.clear();
        processedNs.addAll(wNs);
    }

    public static <T> T PRMin(Collection<T> eles, BinaryFunction<T, T, ? extends Number> comparator)
    {
        var g = new Graph<T>();
        var ar = Utilities.makeArrayList(eles);
        for (var ele : ar)
            g.addVertex(ele);
        for (var i = 0; i <= ar.size() - 2; i++)
        {
            var iEle = ar.get(i);
            for (var j = i + 1; j <= ar.size() - 1; j++)
            {
                var jEle = ar.get(j);
                var comp = comparator.apply(iEle, jEle).doubleValue();
                if (comp < 0)
                    g.addEdge(iEle, jEle);
                else if (comp > 0)
                    g.addEdge(jEle, iEle);
            }
        }
        Utilities.map((ArrayList<T> ed) ->
        {
            g.setEdgeWeight(ed, 1d);
        }, g.edgeList());
        var opts = new HashMap<String, Object>();
        opts.put("Step Number", 100);
        opts.put("Show Progress", false);
        var pR = Graph.pageRank(g, opts);
        Utilities.sortBy(ar, (x) -> pR.get(x));
//        System.out.println(
//                "soted ranks " + Utilities.map((T x) -> pR.get(x), ar)
//        );
        return ar.get(0);
    }

    public static Graph<WordVertex> recursiveMaxTree(Graph<WordVertex> g, HashMap<String, Object> opts)
    {
        final var vs = g.vertexList();
        ArrayList<WordVertex> processedVs;
        if (Utilities.anyTrue(vs, (x) ->
        {
            var check0 = x.Type.equals("V");
            var check1 = g.vertexInComponent(x).size() == g.vertexCount();
            var check2 = Utilities.anyTrue(vs,
                    (y) -> y.Location > x.Location
            );
            return check0 && check1 && check2;
        }))
            return recursiveMaxTree(g,
                    (x) -> getProcessingVertices(x),
                    (storedMaxTrees) ->
                    {
                        var vMaxTrees = Utilities.select(storedMaxTrees,
                                (maxTree) ->
                                {
                                    var root = Utilities.firstCase(maxTree.vertexList(),
                                            (x) -> maxTree.vertexOutDegree(x) == 0
                                    );
                                    return root.Type.equals("V");
                                }
                        );
                        return findQuickMinimal(vMaxTrees, (Graph<WordVertex> tree0, Graph<WordVertex> tree1) ->
                        {
                            return errorTreeCompare(tree0, tree1);
                        });
                    }, opts
            );
        else return recursiveMaxTree(g,
                (Graph<WordVertex> h) ->
                {
                    ArrayList<WordVertex> res = getLegitimateProcessingVertices(h);
                    if (Utilities.anyTrue(res, (x) ->
                    {
                        var auxInvs = h.vertexInComponent(x);
                        return (x.Type.startsWith("N") || x.Type.equals("P")) && (auxInvs.size() == h.vertexCount());
                    }))
                        res = Utilities.select(res,
                                (x) ->
                                {
                                    return (x.Type.startsWith("N") || x.Type.equals("P")) || x.Type.equals("E");
                                }
                        );
                    Utilities.sortBy(res, (WordVertex x) -> -x.Location);
                    normalizeProcessingNouns(res);
                    return res;
                },
                (ArrayList<Graph<WordVertex>> storedMaxTrees) ->
                {
                    var auxTrees = Utilities.select(storedMaxTrees,
                            (tree) ->
                            {
                                var treeRoot = getRoot(tree);
                                return !treeRoot.Type.equals("E");
                            }
                    );
                    if (auxTrees.size() == 0)
                        auxTrees = storedMaxTrees;
                    return findQuickMinimal(auxTrees,
                            (tree0, tree1) -> errorTreeCompare(tree0, tree1)
                    );
                }, opts
        );
    }

    public static double toRootDistanceVariance(Graph<WordVertex> tree)
    {
        var leaves = Utilities.select(tree.vertexList(),
                (x) -> tree.vertexInDegree(x) == 0
        );
        var dists = Utilities.map((WordVertex x) -> toRootDistance(tree, x), leaves);
        return Utilities.variance(dists);
    }

    /**
     * hàm này sẽ xử lý các đỉnh từ vị trí lớn nhất đến nhỏ dần bằng cách cho nó lên gốc
     *
     * @param g          đồ thị gốc
     * @param procVsFunc hàm chọn các đỉnh để xử lý và sắp xếp lại các đỉnh được xử lý, các đỉnh ở đầu dãy sẽ được xử lý trước
     * @param returnFunc hàm này chọn cây được trả lại
     * @param opts
     * @return trả lại cây được chọn theo hàm returnFunc
     */
    public static Graph<WordVertex> recursiveMaxTree(Graph<WordVertex> g,
                                                     UnaryFunction<Graph<WordVertex>, ArrayList<WordVertex>> procVsFunc,
                                                     UnaryFunction<ArrayList<Graph<WordVertex>>, Graph<WordVertex>> returnFunc,
                                                     HashMap<String, Object> opts)
    {
        Collection<WordVertex> removedProcVs;
        if (opts.containsKey("Excluded Processed Vertices"))
            removedProcVs = (Collection<WordVertex>) opts.get("Excluded Processed Vertices");
        else removedProcVs = new HashSet<WordVertex>();
        var procVs = procVsFunc.apply(g);
        if (procVs.size() > 0)
        {
            if (!Utilities.containsAll(removedProcVs, procVs))
                Utilities.deleteCases(procVs,
                        (x) -> removedProcVs.contains(x)
                );
            else
            {
                var copiedG = g.clone();
                var prOpts = new HashMap<String, Object>();
                prOpts.put("Step Number", 100);
                prOpts.put("Show Progress", false);
                var pR = Graph.pageRank(copiedG, prOpts);
                var maxV = Utilities.maxBy(procVs, (x) -> pR.get(x));
                procVs.clear();
                procVs.add(maxV);
            }
        }
        if (procVs.size() == 0)
        {
            var res = (Graph) g.clone();
            res.setGraphProperty("origin graph", g.clone());
            /*res.setGraphProperty("other trees", new CustomArrayList<Graph<WordVertex>>(new Graph[]{(Graph) g.clone()}));*/
            return res;
        }
        var runningg = (Graph<WordVertex>) g.clone();
        Graph<WordVertex> maxTree = null;
        var storedMaxTrees = new ArrayList<Graph<WordVertex>>();
        for (var root : procVs)
        {
            maxTree = maximumSpanningTree(runningg, root, opts);
            var indices = Utilities.makeHashSet(Utilities.map((WordVertex x) -> x.Location, runningg.vertexList()));
            if (maxTree.vertexCount() == indices.size() /*runningg.vertexCount()*/)
                storedMaxTrees.add(maxTree);
            /*maxTree.setGraphProperty("errors", countErrors(maxTree, true));*/
            maxTree.setGraphProperty("origin graph", runningg.clone());
            var cutIndex = root.Location;
            var subMaxTree = maxTree.subgraph(
                    Utilities.select(maxTree.vertexList(),
                            (x) -> x.Location >= cutIndex
                    )
            );
            var removedVs = Utilities.select(g.vertexList(),
                    (v) ->
                    {
                        var subMaxTreeVs = subMaxTree.vertexList();
                        return Utilities.anyTrue(subMaxTreeVs,
                                (x) -> x.Location == v.Location && !x.equals(v)
                        );
                    }
            );
            var removedEds = Utilities.select(g.edgeList(),
                    (ed) ->
                    {
                        var v0 = ed.get(0);
                        var v1 = ed.get(1);
                        return subMaxTree.containsVertex(v0) && subMaxTree.containsVertex(v1) && !subMaxTree.containsEdge(ed) && !isFragileVertex(subMaxTree, v0)
                                || subMaxTree.containsVertex(v0) && !subMaxTree.containsVertex(v1) && subMaxTree.vertexOutDegree(v0) != 0 && !isFragileVertex(subMaxTree, v0)
                                || !subMaxTree.containsVertex(v0) && subMaxTree.containsVertex(v1) && subMaxTree.vertexOutDegree(v1) != 0;
                    }
            );
            runningg = (Graph) g.clone();
            runningg.deleteVertices(removedVs);
            runningg.deleteEdges(removedEds);
        }
        Graph<WordVertex> res;
        try
        {
            res = returnFunc.apply(storedMaxTrees);
        } catch (Exception e)
        {
            Utilities.executeMathematicaCode("Echo[%0@toString[]]", procVs);
            Utilities.executeMathematicaCode("Echo[%0@toString[]]", g);
            throw new RuntimeException(e.getMessage());
        }
        return returnFunc.apply(storedMaxTrees);
    }

    public static ArrayList<WordVertex> getLegitimateProcessingVertices(Graph<WordVertex> g)
    {
        var vs = g.vertexList();
        var strongVs = Utilities.select(vs,
                (v) -> g.vertexInComponent(v).size() == vs.size()
        );
        var res = new ArrayList<WordVertex>();
        if (strongVs.size() == 0)
            return res;
        var maxStrongV = Utilities.maxBy(strongVs,
                (x) -> x.Location
        );
        Utilities.sortBy(strongVs, (x) -> -x.Location);
        var auxg = (Graph<WordVertex>) g.clone();
        auxg.deleteVertices(strongVs);
        var subReses = new ArrayList<ArrayList<WordVertex>>();
        var compos = auxg.weaklyConnectedComponents();
        for (var compo : compos)
        {
            var subg = auxg.subgraph(compo);
            subReses.add(getLegitimateProcessingVertices(subg));
        }
        for (var subRes : subReses)
            res.addAll(subRes);
        Utilities.sortBy(res, (x) -> -x.Location);
        Utilities.deleteCases(res,
                (x) -> x.Location < maxStrongV.Location
        );
        res.addAll(strongVs);
        return res;
    }

    public static ArrayList<WordVertex> getProcessingVertices(Graph<WordVertex> g)
    {
        var vs = Utilities.makeArrayList(getLegitimateProcessingVertices(g)/*g.vertexList()*/);
        vs = Utilities.select(vs,
                (v) -> v.Type.equals("V") || v.Type.equals("E") || (v.Type.equals("C") && v.Word.equals("rằng")) || v.isAdditionalProcessedVertex
        );
        var gVs = g.vertexList();
        Utilities.deleteCases(vs,
                (x) -> x.Type.equals("V") && !Utilities.anyTrue(gVs,
                        (y) -> y.Location > x.Location
                )
        );
        Utilities.sortBy(vs,
                (x) -> -x.Location
        );
        while (vs.size() > 0 && Utilities.getLastElement(vs).Type.equals("E"))
            vs.remove(vs.size() - 1);
        return vs;
    }

    public static boolean isErrorEdge(Graph<WordVertex> tree, ArrayList<WordVertex> ed)
    {
        var errors = countErrors(tree);
        return Utilities.anyTrue(errors.keySet(),
                name ->
                {
                    var errorSet = (HashSet) errors.get(name);
                    return /*errorSet.contains(ed)||*/Utilities.isIntersecting(errorSet, ed) || Utilities.isIntersecting(errorSet,
                            NullFunction.createInstance(() ->
                            {
                                var res = new ArrayList<>();
                                res.add(ed);
                                return res;
                            }).apply()
                    );
                }
        );
    }

    public static boolean isFragileVertex(Graph<WordVertex> tree, WordVertex v)
    {
        try
        {
            var ed = Utilities.firstCase(tree.edgeList(),
                    x -> x.get(0).equals(v)
            );
            return isErrorEdge(tree, ed);
        } catch (Exception e)
        {
            return false;
        }
//        if (tree.vertexOutDegree(v) == 0)
//            return false;
//        var v1 = Utilities.getFirstElement(tree.outGoingVertices(v));
//        var ed = new CustomArrayList<WordVertex>(new WordVertex[]{v, v1});
//        return !isTrustedEdge(ed);
    }

    public static int countViolations(Graph<WordVertex> tree)
    {
        var composes = tree.weaklyConnectedComponents();
        if (composes.size() <= 1)
        {
            if (tree.vertexCount() == 0)
                return 0;
            var violations = Utilities.map((WordVertex x) ->
            {
                return countViolations(tree, x.Location);
            }, tree.vertexList());
            var res = Utilities.sum(violations);
            return Double.valueOf(res).intValue();
        } else
        {
            return (int) Utilities.sum(
                    compos ->
                    {
                        var subG = tree.subgraph(compos);
                        return countViolations(subG);
                    }, composes);
        }
    }

    private static int countViolations(Graph<WordVertex> tree, int loc)
    {
        var root = Utilities.firstCase(tree.vertexList(),
                (x) -> tree.vertexOutDegree(x) == 0
        );
        var vs = tree.vertexList();
        var locs = Utilities.map((WordVertex x) -> x.Location, vs);
        if (locs.contains(loc))
        {
            var res = 0;
            var inVs = tree.inGoingVertices(root);
            for (var v : inVs)
            {
                var inCompos = tree.vertexInComponent(v);
                var subTree = tree.subgraph(inCompos);
                res += countViolations(subTree, loc);
            }
            return res;
        } else
        {
            var min = Utilities.min(locs, (x, y) -> x.intValue() - y.intValue());
            var max = Utilities.max(locs, (x, y) -> x.intValue() - y.intValue());
            if (loc < min || loc > max)
                return 0;
            else
            {
                var res = 0;
                var inVs = tree.inGoingVertices(root);
                for (var v : inVs)
                {
                    var inCompos = tree.vertexInComponent(v);
                    var subTree = tree.subgraph(inCompos);
                    res += countViolations(subTree, loc);
                }
                if (res != 0)
                    return res;
                else return 1;
            }
        }
    }

    public static boolean isWordOutside(Graph<WordVertex> g, WordVertex v)
    {
        return Utilities.allTrue(g.inGoingVertices(v),
                (x) -> isAdverb(g, x)
        );
        /*return isWordInLocation(g, v, AuxiliaryTypes, "outside");*/
    }

    public static boolean isWordInside(Graph<WordVertex> g, WordVertex v)
    {
        return Utilities.anyTrue(g.inGoingVertices(v),
                (x) -> !isAdverb(g, x)
        );
//        return isWordInLocation(g, v, AuxiliaryTypes, "inside");
    }

    public static boolean isWordInLocation(Graph<WordVertex> g, WordVertex v, HashSet<String> nonEssentialTypes, String location)
    {
        var inVs = g.inGoingVertices(v);
        var count = Utilities.count(inVs,
                (x) -> nonEssentialTypes.contains(x.Type)
        );
        if (location.equals("inside"))
            return inVs.size() != count;
        if (location.equals("outside"))
            return inVs.size() == count;
        throw new RuntimeException("isWordInLocation error");
    }

//    public static boolean fixCompoundNounProblems(Graph<WordVertex> tree)
//    {
//        var res = false;
//        while (true)
//        {
//            var check0 = false/*fixHorizontalConsecutiveNouns(tree)*/;
//            var check1 = fixVerticalNouns(tree);
//            res = res || check0 || check1;
//            if (!check0 && !check1)
//                break;
//        }
//        return res;
//    }

    public static boolean fixVerticalNouns(Graph<WordVertex> g, Graph<WordVertex> tree)
    {
        for (var v : tree.vertexList())
        {
            var inVs = tree.vertexInComponent(v);
            if (inVs.size() <= 1)
                continue;
            if (!Utilities.allTrue(inVs, (x) -> (isNoun(x) || x.Type.equals("P") || x.Type.equals("M") || x.Type.equals("L") || x.Type.equals("A"))))
                continue;
            if (!Utilities.anyTrue(inVs, (x) -> isNoun(x)))
                continue;
//            var fixedNG = makeCompoundNoun(inVs);
            Graph<WordVertex> fixedNG;
            var subg = g.subgraph(inVs);
//            Utilities.executeMathematicaCode("Echo[%0@toString[]]",subg);
            var opts = new HashMap<String, Object>();
            opts.put("storeVerbRoots", false);
            fixedNG = strongRecursiveMaxTree(subg, opts);

            var subtree = tree.subgraph(inVs);
            if (parserSameQ(fixedNG, subtree))
                continue;
            var outVs = tree.outGoingVertices(v);
            if (outVs.size() > 0)
            {
                var aboveV = Utilities.getFirstElement(outVs);
                tree.deleteEdge(v, aboveV);
                var root = Utilities.firstCase(fixedNG.vertexList(), x -> fixedNG.vertexOutDegree(x) == 0);
                tree.addEdge(root, aboveV);
            }
            tree.deleteEdges(subtree.edgeList());
            tree.addEdges(fixedNG.edgeList());
            return true;
        }
        return false;
    }

    private static boolean parserSameQ(Graph<WordVertex> g0, Graph<WordVertex> g1)
    {
        if (g0.vertexCount() != g1.vertexCount())
            return false;
        if (g0.edgeCount() != g1.edgeCount())
            return false;
        for (var ed : g0.edgeList())
            if (!g1.containsEdge(ed))
                return false;
        return true;
    }

    private static boolean fixHorizontalConsecutiveNouns(Graph<WordVertex> tree)
    {
        var nounCompounds = getHorizontalNounCompounds(tree);
        if (nounCompounds.size() == 0)
            return false;
        for (var nounComp : nounCompounds)
        {
            var firstV = Utilities.getFirstElement(nounComp);
            var aboveV = Utilities.getFirstElement(tree.outGoingVertices(firstV));
            var nounG = makeCompoundNoun(nounComp);
            var root = Utilities.firstCase(nounG.vertexList(),
                    (x) -> nounG.vertexOutDegree(x) == 0
            );
            for (var v : nounComp)
                tree.deleteEdge(v, aboveV);
            tree.addEdge(root, aboveV);
            for (var ed : nounG.edgeList())
                tree.addEdge(ed);
        }
        return true;
    }

    private static HashSet<HashSet<WordVertex>> getHorizontalNounCompounds(Graph<WordVertex> tree)
    {
        var compoundG = new Graph<WordVertex>();
        for (var v : tree.vertexList())
            compoundG.addVertex(v);
        UnaryFunction<String, String> simplifyN = (x) ->
        {
            if (x.startsWith("N"))
                return "N";
            else return x;
        };
        var typeHs = new CustomHashSet<String>(new String[]{"N", "L", "M", "P"});
        for (var v : tree.vertexList())
        {
            var inVs = Utilities.makeArrayList(tree.inGoingVertices(v));
            Utilities.quickSort(inVs, (x, y) -> x.Location - y.Location);
            for (var i = 0; i <= inVs.size() - 2; i++)
            {
                var iEle = inVs.get(i);
                var nextIEle = inVs.get(i + 1);
                var vLoc = v.Location;
                if (nextIEle.Location < vLoc || iEle.Location > vLoc)
                {
                    var type0 = simplifyN.apply(iEle.Type);
                    var type1 = simplifyN.apply(nextIEle.Type);
                    if (typeHs.contains(type0) && typeHs.contains(type1))
                        compoundG.addEdge(iEle, nextIEle);
                }
            }
        }
        var wcompos = compoundG.weaklyConnectedComponents();
        var res = Utilities.select(wcompos,
                (compos) ->
                {
                    return compos.size() > 1 && Utilities.memberQ(compos,
                            (x) -> isNoun(x)
                    );
                }
        );
        return Utilities.makeHashSet(res);
    }

    private static Graph<WordVertex> makeCompoundNoun(Collection<WordVertex> words)
    {
        var auxWords = Utilities.select(words,
                (x) -> x.Type.equals("L") || x.Type.equals("M") || x.Type.equals("A") || x.Type.equals("P")
        );
        var nouns = Utilities.select(words,
                (x) -> isNoun(x)
        );
        Utilities.quickSort(nouns, (x, y) -> x.Location - y.Location);
        var res = new Graph<WordVertex>();
        for (var word : words)
            res.addVertex(word);
        for (var i = nouns.size() - 1; i >= 1; i--)
        {
            var a = nouns.get(i);
            var b = nouns.get(i - 1);
            res.addEdge(a, b);
        }
        var mainWord = nouns.get(0);
        for (var auxWord : auxWords)
            res.addEdge(auxWord, mainWord);
        return res;
    }

    private static boolean isNoun(WordVertex v)
    {
        var type = v.Type;
        return type.startsWith("N");
    }

    public static double getInsideOutsideLeastSquares()
    {
        if (InsideOutsideLeastSquares != null)
            return InsideOutsideLeastSquares;
        if (WordInsideOutsides == null)
            getWordInsideOutsides();
        var data = new ArrayList<ArrayList<Double>>();
        for (var wordInfo : WordInsideOutsides.keySet())
        {
            var freq = WordInsideOutsides.get(wordInfo);
            var pair = new ArrayList<Double>();
            if (freq.size() == 1)
                pair.add(0d);
            for (var dir : freq.keySet())
                pair.add(freq.get(dir).doubleValue());
            Utilities.quickSort(pair, (x, y) -> x.doubleValue() - y.doubleValue());
            data.add(pair);
        }
        InsideOutsideLeastSquares = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data).get(0);
        return InsideOutsideLeastSquares;
    }

    public static Double InsideOutsideLeastSquares = null;
    public static HashMap<ArrayList<String>, HashMap<String, Integer>> WordInsideOutsides = null;
    public static Double strongEssentialOutsideThresold = null;

    public static HashMap<ArrayList<String>, HashMap<String, Integer>> removedPluralInsideOutside = null;

//    public static void initializeStrongEssentialOutsideThresold()
//    {
//        if (InsideOutSide == null)
//            getInsideOutside();
//        var data = new ArrayList<Double>();
//        final var insideStr = "inside";
//        final var outsideStr = "outside";
//        for (var wordInfo : InsideOutSide.keySet())
//        {
//            var map = InsideOutSide.get(wordInfo);
//            var inside = 0d;
//            var outside = 0d;
//            if (map.containsKey(outsideStr))
//                outside = map.get(outsideStr).doubleValue();
//            if (map.containsKey(insideStr))
//                inside = map.get(insideStr).doubleValue();
//            data.add((outside + 1) / (inside + 1));
//        }
//        strongEssentialOutsideThresold = Utilities.mean(data) + Utilities.variance(data);
//    }

//    public static void initializeRemovedPluralMLInsideOutside()
//    {
//        removedPluralInsideOutside = new HashMap<>();
//        processInsideOutside(new CustomHashSet<String>(new String[]{"L", "M"}), removedPluralInsideOutside);
//    }

//    public static void initializeInsideOutside()
//    {
//        InsideOutSide = new HashMap<>();
//        getInsideOutside(/*AuxiliaryTypes, */InsideOutSide);
//    }

    private final static HashSet<String> AuxiliaryTypes = new CustomHashSet<String>(new String[]{/*"R", "L", "M"*/});

    public static HashMap<ArrayList<String>, HashMap<String, Integer>> getWordInsideOutsides()
    {
        if (WordInsideOutsides != null)
            return WordInsideOutsides;
        var res = new HashMap<ArrayList<String>, HashMap<String, Integer>>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                var word = v.Word;
                var type = v.Type;
                var pair = new CustomArrayList<String>(new String[]{word, type});
                Utilities.insertValue(res, new Object[]{pair,
                                isWordOutside(tree, v) ? "outside" : "inside"
                        },
                        0, (x) -> x + 1
                );
            }
        }
        WordInsideOutsides = res;
        return WordInsideOutsides;
    }

    public static HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>> getTypeTernaryDirections()
    {
        var res = new HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>>();
        UnaryFunction<String, String> simplifyN = (x) ->
        {
            if (x.startsWith("N"))
                return "N";
            else return x;
        };
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            for (var v : g.vertexList())
            {
                var inVs = Utilities.makeArrayList(g.inGoingVertices(v));
                Utilities.quickSort(inVs, (x, y) -> x.Location - y.Location);
                for (var i = 0; i <= inVs.size() - 2; i++)
                {
                    var iEle = inVs.get(i);
                    var nextIEle = inVs.get(i + 1);
                    var types = new ArrayList<String>();
                    types.add(simplifyN.apply(v.Type));
                    types.add(simplifyN.apply(iEle.Type));
                    types.add(simplifyN.apply(nextIEle.Type));
                    var locs = new ArrayList<Integer>();
                    locs.add(v.Location);
                    locs.add(iEle.Location);
                    locs.add(nextIEle.Location);
                    locs = simplifyIndices(locs);
                    if (!Utilities.keySequenceExistsQ(res, types, locs))
                        Utilities.insertValue(res, new Object[]{types, locs}, 0);
                    var value = Utilities.getValue(res, types, locs);
                    Utilities.insertValue(res, new Object[]{types, locs}, ((int) value) + 1);
                }
            }
        }
        return res;
    }

    public static Double typePairDirectionLeastSquares = null;

    public static void initializeTypePairDirectionLeastSquares()
    {
        typePairDirectionLeastSquares = getTypePairDirectionLeastSquares();
    }

    public static double getTypePairDirectionLeastSquares()
    {
        if (typePairDirections == null)
            initializetypePairDirections();
        var data = new ArrayList<ArrayList<Double>>();
//        var vt = new ArrayList<Double>();
        for (var typePair : typePairDirections.keySet())
        {
            var values = new ArrayList<Double>();
            values.add(typePairDirections.get(typePair).get("next").doubleValue());
            values.add(typePairDirections.get(typePair).get("before").doubleValue());
            Utilities.quickSort(values, (x, y) -> x.doubleValue() - y.doubleValue());
            data.add(values);
//            mt.add(values.get(0));
//            vt.add(values.get(1));
        }
        var res = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        return res.get(0);
//        var lb0 = new LoopbackLink();
//        var lb1 = new LoopbackLink();
//        var size = mt.size();
//        lb0.putFunction("List", size);
//        lb1.putFunction("List", size);
//        for (var i = 0; i <= size - 1; i++)
//        {
//            lb0.putFunction("List", 1);
//            lb0.put(mt.get(i));
//            lb1.put(vt.get(i));
//        }
//        var lb2 = new LoopbackLink();
//        lb2.putFunction("LeastSquares", 2);
//        lb2.put(lb0.getExpr());
//        lb2.put(lb1.getExpr());
//        try
//        {
//            return Utilities.evaluateExpr(lb2.getExpr()).part(1).asDouble();
//        } catch (Exception e)
//        {
//            throw new RuntimeException(e.getMessage());
//        }
    }

    /**
     * ở đây các danh từ được đơn giản hóa ví dụ như Np trờ thành N
     */
    public static HashMap<ArrayList<String>, HashMap<String, Integer>> typePairDirections = null;

    public static void initializetypePairDirections()
    {
        typePairDirections = getTypePairDirections();
    }

    private static HashMap<ArrayList<String>, HashMap<String, Integer>> getTypePairDirections()
    {
        var res = new HashMap<ArrayList<String>, HashMap<String, Integer>>();
        final var next = "next";
        final var before = "before";
        UnaryFunction<String, String> simplifyType = (x) ->
        {
            if (x.startsWith("N"))
                return "N";
            else return x;
        };
        for (var parser : Parsers)
        {
            var auxg = getDependenceGraph(parser);
            for (var ed : auxg.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var direction = v0.Location < v1.Location ? next : before;
                var typePair = new CustomArrayList<String>(new String[]{simplifyType.apply(v0.Type), simplifyType.apply(v1.Type)});
                if (!res.containsKey(typePair))
                {
                    res.put(typePair, new HashMap<String, Integer>());
                    res.get(typePair).put(before, 0);
                    res.get(typePair).put(next, 0);
                }
                switch (direction)
                {
                    case next:
                        var value = res.get(typePair).get(next);
                        res.get(typePair).put(next, value + 1);
                        break;
                    case before:
                        value = res.get(typePair).get(before);
                        res.get(typePair).put(before, value + 1);
                        break;
                }
            }
        }
        return res;
    }

    public static double waitingWordThresold;
    public static double nonWaitingWordThresold;

    public static boolean isWaitingEdgeQ(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        var v0 = ed.get(0);
        var v1 = ed.get(1);
        var w0 = g.getVertexWeight(v0);
        var w1 = g.getVertexWeight(v1);
        var edW = g.getEdgeWeight(ed);
        var ar = new CustomArrayList<Double>(new Double[]{w0, w1, edW});
        var sum = 0d;
        for (var i = 0; i <= ar.size() - 1; i++)
            sum += (ar.get(i) * waitingEdgeLeastSquares.get(i));
        return sum >= waitingWordThresold;
    }

    public static boolean isEssentialInsideWordQ(WordVertex v)
    {
        var waMean = getWordAppearanceMean();
        var waVariance = getWordAppearanceVariance();
        var vAp = WordAppearances.get(v.Word).get(v.Type);
        if (vAp > waMean + waVariance)
            return isLocationEssentialWordQ(v, "inside");
        else return false;
    }

    public static boolean isEssentialOutsideWordQ(WordVertex v)
    {
        var waMean = getWordAppearanceMean();
        var waVariance = getWordAppearanceVariance();
        var vAp = WordAppearances.get(v.Word).get(v.Type);
        if (vAp > waMean + waVariance)
            return isLocationEssentialWordQ(v, "outside");
        else return false;
    }

//    public static boolean isStrongEssentialOutsideWord(WordVertex v)
//    {
//        if (v.Type.equals("V"))
//            return false;
//        if (strongEssentialOutsideThresold == null)
//            initializeStrongEssentialOutsideThresold();
//        var wordInfo = new CustomArrayList<String>(new String[]{v.Word, v.Type});
//        var freq = InsideOutSide.get(wordInfo);
//        var inside = 0;
//        var outside = 0;
//        final var insideStr = "inside";
//        final var outsideStr = "outside";
//        if (freq.containsKey(insideStr))
//            inside = freq.get(insideStr);
//        if (freq.containsKey(outsideStr))
//            outside = freq.get(outsideStr);
//        return (((double) (outside + 1)) / (inside + 1)) >= strongEssentialOutsideThresold.doubleValue();
//    }

    public static boolean isLocationEssentialWordQ(WordVertex v, String loc)
    {
        if (InsideOutsideLeastSquares == null)
            getInsideOutsideLeastSquares();
        var wordInfo = new CustomArrayList<String>(new String[]{v.Word, v.Type});
        var freq = WordInsideOutsides.get(wordInfo);
        var inside = 0;
        var outside = 0;
        final var insideStr = "inside";
        final var outsideStr = "outside";
        if (freq.containsKey(insideStr))
            inside = freq.get(insideStr);
        if (freq.containsKey(outsideStr))
            outside = freq.get(outsideStr);
        if (loc.equals(insideStr))
        {
            return inside > outside * InsideOutsideLeastSquares;
        } else if (loc.equals(outsideStr))
        {
            return outside > inside * InsideOutsideLeastSquares;
        } else throw new RuntimeException("isEssentialLocationWord unexpected");
    }

    public static int getTreeHeight(Graph<WordVertex> tree)
    {
        try
        {
            var vs = tree.vertexList();
            var borders = Utilities.select(vs,
                    (x) -> tree.vertexInDegree(x) == 0
            );
            var distances = Utilities.map((WordVertex x) ->
            {
                return toRootDistance(tree, x);
            }, borders);
            return Utilities.max(distances, (x, y) -> x.intValue() - y.intValue());
        } catch (Exception e)
        {
            Utilities.executeMathematicaCode("MyCounterexample=%0", tree);
            throw new RuntimeException(e.getMessage());
        }
    }

    public static Double waitingWordLeastSquares = null;
    public static ArrayList<Double> waitingEdgeLeastSquares = null;

    public static void initializeWaitingElements(HashMap<Object, Double> PR)
    {
        waitingWordLeastSquares = getWaitingWordLeastSquares(PR);
        var treeHeights = new ArrayList<Integer>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            if (tree.vertexCount() == 0)
                continue;
            treeHeights.add(getTreeHeight(tree));
        }
        var mean = Utilities.mean(treeHeights);
        var variance = Utilities.variance(treeHeights);
        waitingWordThresold = 1d / (3 * (mean + variance));
        nonWaitingWordThresold = 1d / (160 * (mean + variance));
    }

    public static int maximumDistanceToBoundary(Graph<WordVertex> tree, WordVertex v)
    {
        var inVs = tree.vertexInComponent(v);
        var boundaryVs = Utilities.select(inVs,
                (x) -> tree.vertexInDegree(x) == 0
        );
        var distances = Utilities.map((WordVertex x) ->
        {
            var path = tree.findPath(x, v);
            return path.size() - 1;
        }, boundaryVs);
        return Utilities.max(distances, (x, y) -> x.intValue() - y.intValue());
    }

    public static ArrayList<Double> getWaitingEdgeLeastSquares(HashMap<EdgeVertex, Double> EdPR, HashMap<Object, Double> PR)
    {
        var mt = new ArrayList<ArrayList<Double>>();
        var vt = new ArrayList<Double>();
        UnaryFunction<WordVertex, ArrayList<String>> getPair = (v) ->
        {
            var res = new ArrayList<String>();
            res.add(v.Word);
            res.add(v.Type);
            return res;
        };
        for (var parser : VietnameseAnalyzer.Parsers)
        {
            var auxg = getDependenceGraph(parser);
            var eds = auxg.edgeList();
            for (var ed : eds)
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var tail = getPair.apply(v0);
                var head = getPair.apply(v1);
                var direction = v0.Location < v1.Location ? "next" : "before";
                var edV = new EdgeVertex(tail, head);
                edV.Direction = direction;
                if (PR.containsKey(tail) && PR.containsKey(head) && EdPR.containsKey(edV))
                {
                    var tuple = new ArrayList<Double>();
                    tuple.add(PR.get(tail));
                    tuple.add(PR.get(head));
                    tuple.add(EdPR.get(edV));
                    mt.add(tuple);
                    if (auxg.vertexInDegree(v0) == 0)
                        vt.add(0d);
                    else vt.add(1d);
                }
            }
        }
        var lb0 = new LoopbackLink();
        var lb1 = new LoopbackLink();
        var size = mt.size();
        lb0.putFunction("List", size);
        lb1.putFunction("List", size);
        for (var i = 0; i <= size - 1; i++)
        {
            var tuple = mt.get(i);
            lb0.putFunction("List", tuple.size());
            for (var value : tuple)
                lb0.put(value);
            lb1.put(vt.get(i));
        }
        var mtExpr = lb0.getExpr();
        var vtExpr = lb1.getExpr();
        var lb2 = new LoopbackLink();
        lb2.putFunction("LeastSquares", 2);
        lb2.put(mtExpr);
        lb2.put(vtExpr);
        var exprRes = Utilities.evaluateExpr(lb2.getExpr());
        var res = new ArrayList<Double>();
        try
        {
            for (var i = 1; i <= exprRes.length(); i++)
                res.add(exprRes.part(i).asDouble());
            return res;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static double getWaitingWordLeastSquares(HashMap<Object, Double> PR)
    {
        var mt = new ArrayList<Double>();
        var vt = new ArrayList<Double>();
        for (var parser : VietnameseAnalyzer.Parsers)
        {
            var auxg = getDependenceGraph(parser);
            for (var v : auxg.vertexList())
            {
                var word = v.Word;
                var type = v.Type;
                var pair = new CustomArrayList<String>(new String[]{word, type});
                if (PR.containsKey(pair))
                {
                    var value = PR.get(pair);
                    mt.add(value);
                    var dist0 = toRootDistance(auxg, v);
                    var dist1 = maximumDistanceToBoundary(auxg, v);
                    var dist = dist0 + dist1;
                    if (dist == 0)
                        vt.add(0d);
                    else
                    {
                        vt.add(((double) dist1) / dist);
                    }
                }
            }
        }
        var lb0 = new LoopbackLink();
        var lb1 = new LoopbackLink();
        lb0.putFunction("List", vt.size());
        lb1.putFunction("List", vt.size());
        for (var i = 0; i <= vt.size() - 1; i++)
        {
            lb0.putFunction("List", 1);
            lb0.put(mt.get(i));
            lb1.put(vt.get(i));
        }
        var mtExpr = lb0.getExpr();
        var vtExpr = lb1.getExpr();
        var lb2 = new LoopbackLink();
        lb2.putFunction("LeastSquares", 2);
        lb2.put(mtExpr);
        lb2.put(vtExpr);
        try
        {
            return Utilities.evaluateExpr(lb2.getExpr()).part(1).asDouble();
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static void initializeToSecondLevelLeastSquares(HashMap<EdgeVertex, Double> EdPR,
                                                           HashMap<ArrayList<String>, Double> PR)
    {
        var length = 2;
        toSecondLevelLeastSquares = new LeastSquares();
        var data = getLeastSquaresData(EdPR, PR, length, 1, 0);
        toSecondLevelLeastSquares.Single = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toSecondLevelLeastSquares.SingleVariance = getLeastSquaresVariance(data, toSecondLevelLeastSquares.Single);

        data = getLeastSquaresData(EdPR, PR, length, 2, 0);
        toSecondLevelLeastSquares.Left = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toSecondLevelLeastSquares.LeftVariance = getLeastSquaresVariance(data, toSecondLevelLeastSquares.Left);

        data = getLeastSquaresData(EdPR, PR, length, 2, 1);
        toSecondLevelLeastSquares.Right = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toSecondLevelLeastSquares.RightVariance = getLeastSquaresVariance(data, toSecondLevelLeastSquares.Right);

        data = getLeastSquaresData(EdPR, PR, length, 3, 1);
        toSecondLevelLeastSquares.Between = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toSecondLevelLeastSquares.BetweenVariance = getLeastSquaresVariance(data, toSecondLevelLeastSquares.Between);
    }

    public static void initializeToFirstLevelLeastSquares(HashMap<EdgeVertex, Double> EdPR, HashMap<ArrayList<String>, Double> PR)
    {
        toFirstLevelLeastSquares = new LeastSquares();
        UnaryFunction<Graph<WordVertex>, Graph<WordVertex>> preprocess = (g) -> g;
        var data = getLeastSquaresData(EdPR, PR, preprocess, 1, 1, 0);
        toFirstLevelLeastSquares.Single = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toFirstLevelLeastSquares.SingleVariance = getLeastSquaresVariance(data, toFirstLevelLeastSquares.Single);

        data = getLeastSquaresData(EdPR, PR, preprocess, 1, 2, 0);
        toFirstLevelLeastSquares.Left = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toFirstLevelLeastSquares.LeftVariance = getLeastSquaresVariance(data, toFirstLevelLeastSquares.Left);

        data = getLeastSquaresData(EdPR, PR, preprocess, 1, 2, 1);
        toFirstLevelLeastSquares.Right = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toFirstLevelLeastSquares.RightVariance = getLeastSquaresVariance(data, toFirstLevelLeastSquares.Right);

        data = getLeastSquaresData(EdPR, PR, preprocess, 1, 3, 1);
        toFirstLevelLeastSquares.Between = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data);
        toFirstLevelLeastSquares.BetweenVariance = getLeastSquaresVariance(data, toFirstLevelLeastSquares.Between);
    }

    public static LeastSquares toFirstLevelLeastSquares;
    public static LeastSquares toSecondLevelLeastSquares;

    public static HashMap<ArrayList<String>, ArrayList<Double>> getLeastSquares(HashMap<ArrayList<String>, ArrayList<ArrayList<Double>>> data)
    {
        var res = new HashMap<ArrayList<String>, ArrayList<Double>>();
        for (var types : data.keySet())
        {
            var lS = getLeastSquares((ArrayList<ArrayList<? extends Number>>) (Object) data.get(types));
            res.put(types, lS);
        }
        return res;
    }

    public static ArrayList<Double> getLeastSquares(ArrayList<ArrayList<? extends Number>> data)
    {
        return MathUtilities.leastSquares((ArrayList<ArrayList<Number>>) (Object) data);
    }

    public static double getLeastSquaresVariance(ArrayList<ArrayList<Double>> data, ArrayList<Double> leastSquares)
    {
        var res = 0d;
        var size = leastSquares.size();
        for (var row : data)
        {
            var sum = 0d;
            for (var i = 0; i <= size - 1; i++)
                sum += (row.get(i) * leastSquares.get(i));
            var lastValue = row.get(size);
            res += ((lastValue - sum) * (lastValue - sum));
        }
        res = res / data.size();
        return Math.sqrt(res);
    }

    public static ArrayList<ArrayList<Double>> getLeastSquaresData(HashMap<EdgeVertex, Double> EdPR,
                                                                   HashMap<ArrayList<String>, Double> PR,
                                                                   int length, int width, int loc)
    {
        UnaryFunction<Graph<WordVertex>, Graph<WordVertex>> preprocess = (g) -> g;
        return getLeastSquaresData(EdPR, PR, preprocess, length, width, loc);
    }

    public static ArrayList<ArrayList<Double>> getLeastSquaresData(HashMap<EdgeVertex, Double> EdPR, HashMap<ArrayList<String>, Double> PR, UnaryFunction<Graph<WordVertex>, Graph<WordVertex>> preprocess,
                                                                   int length, int width, int pos)
    {
        var res = new ArrayList<ArrayList<Double>>();
        var size = Parsers.size();
        for (var i = 0; i <= size - 1; i++)
        {
            var parser = Parsers.get(i);
            var g = preprocess.apply(getDependenceGraph(parser));
            var locals = getLocals(g, length, width);
            for (var local : locals)
            {
                var tuple = getTuple(EdPR, PR, local, pos);
                if (!tuple.contains(null))
                    res.add(tuple);
            }
        }
        return res;
    }

    public static ArrayList<Double> getTuple(HashMap<EdgeVertex, Double> EdPR,
                                             HashMap<ArrayList<String>, Double> PR,
                                             Graph<WordVertex> localTree, Object targetPos)
    {
        BinaryFunction<WordVertex, WordVertex, EdgeVertex> getEdgeVertex = (x, y) ->
        {
            var pair0 = new CustomArrayList<String>(new String[]{x.Word, x.Type});
            var pair1 = new CustomArrayList<String>(new String[]{y.Word, y.Type});
            var ed = new EdgeVertex(pair0, pair1);
            ed.Direction = x.Location < y.Location ? "next" : "before";
            return ed;
        };
        var vs = localTree.vertexList();
        var borderVs = Utilities.select(vs,
                (v) -> localTree.vertexInDegree(v) == 0
        );
        Utilities.quickSort(borderVs, (x, y) -> x.Location - y.Location);
        var interchangeV = Utilities.getFirstElement(localTree.outGoingVertices(borderVs.get(0)));
        var root = Utilities.getFirstElement(Utilities.select(vs,
                (v) -> localTree.vertexOutDegree(v) == 0
        ));
        var eles = new ArrayList<Object>();
        var path = localTree.findPath(interchangeV, root);
        for (var i = 0; i <= path.size() - 2; i++)
        {
            var iV = path.get(i);
            var nextIV = path.get(i + 1);
            var ed = getEdgeVertex.apply(iV, nextIV);
            eles.add(0, ed);
        }
        for (var v : borderVs)
        {
            var ed = getEdgeVertex.apply(v, interchangeV);
            eles.add(ed);
        }
        for (var i = path.size() - 1; i >= 0; i--)
            eles.add(path.get(i));
        int intPos = -1;
        if (targetPos instanceof Number)
            intPos = ((Number) targetPos).intValue();
        else intPos = Utilities.firstPosition(borderVs,
                (x) -> x.equals(targetPos)
        );
        for (var i = 0; i <= borderVs.size() - 1; i++)
        {
            if (i != intPos)
                eles.add(borderVs.get(i));
        }
        eles.add(borderVs.get(intPos));
        var tuple = new ArrayList<Double>();
        for (var ele : eles)
        {
            if (ele instanceof EdgeVertex)
                tuple.add(EdPR.get(ele));
            else
            {
                var origin = (WordVertex) ele;
                var pair = new CustomArrayList<String>(new String[]{origin.Word, origin.Type});
                tuple.add(PR.get(pair));
            }
        }
        return tuple;
    }

    public static ArrayList<Graph<WordVertex>> getLocals(Graph<WordVertex> g, int length, int width)
    {
        var res = new ArrayList<Graph<WordVertex>>();
        var vs = g.vertexList();
        for (var v : vs)
        {
            var mVs = Utilities.select(vs,
                    (w) ->
                    {
                        var path = g.findPath(w, v);
                        if (path == null)
                            return false;
                        else return path.size() == length;
                    });
            for (var mV : mVs)
            {
                var path = g.findPath(mV, v);
                var inVs = Utilities.makeArrayList(g.inGoingVertices(mV));
                Utilities.quickSort(inVs, (x, y) -> x.Location - y.Location);
                for (var i = 0; i <= inVs.size() - width; i++)
                {
                    var iwidth = Utilities.part(inVs, i, i + width - 1);
                    var union = Utilities.union(path, iwidth);
                    res.add(g.subgraph(union));
                }
            }
        }
        return res;
    }

    public static ArrayList<Double> attachedToNonRoots(HashMap<EdgeVertex, Double> EdPR, HashMap<Object, Double> PR)
    {
        var data = new ArrayList<ArrayList<Double>>();
        BinaryFunction<Graph<WordVertex>, WordVertex, ArrayList<WordVertex>> pathFunc = (g, v) ->
        {
            var outV = Utilities.getFirstElement(g.outGoingVertices(v));
            var outoutV = Utilities.getFirstElement(g.outGoingVertices(outV));
            return new CustomArrayList<WordVertex>(new WordVertex[]{outoutV, outV, v});
        };
        UnaryFunction<WordVertex, ArrayList<String>> func = (x) ->
        {
            return new CustomArrayList<String>(new String[]{x.Word, x.Type});
        };
        for (var i = 0; i <= Parsers.size() - 1; i++/*var parser : Parsers*/)
        {
            var parser = Parsers.get(i);
            var g = getDependenceGraph(parser);
            for (var v : g.vertexList())
            {
                if (toRootDistance(g, v) >= 2)
                {
                    var path = pathFunc.apply(g, v);
                    if (i == 0)
                        Utilities.executeMathematicaCode("Echo[%0@toString[]]", path);
                    var x = path.get(0);
                    var pairX = func.apply(x);
                    var y = path.get(1);
                    var pairY = func.apply(y);
                    var z = path.get(2);
                    var pairZ = func.apply(z);
                    var xyEd = new EdgeVertex(pairX, pairY);
                    xyEd.Direction = x.Location < y.Location ? "next" : "before";
                    if (!EdPR.containsKey(xyEd))
                        continue;
                    var yzEd = new EdgeVertex(pairY, pairZ);
                    yzEd.Direction = y.Location < z.Location ? "next" : "before";
                    if (!EdPR.containsKey(yzEd))
                        continue;
                    data.add(new CustomArrayList<Double>(new Double[]{
                            PR.get(pairX), EdPR.get(xyEd), PR.get(pairY), EdPR.get(yzEd), PR.get(pairZ)
                    }));
                    if (i == 0)
                        Utilities.executeMathematicaCode("Echo[%0@toString[]]", path);
                }
            }
        }
        Utilities.executeMathematicaCode("MyData=%0", data);
        var loopbackLink0 = new LoopbackLink();
        loopbackLink0.putFunction("List", data.size());
        var loopbackLink1 = new LoopbackLink();
        loopbackLink1.putFunction("List", data.size());
        for (var tuple : data)
        {
            loopbackLink0.putFunction("List", 4);
            for (var i = 0; i <= 3; i++)
                loopbackLink0.put(tuple.get(i));
            loopbackLink1.put(tuple.get(4));
        }
        var mt = loopbackLink0.getExpr();
        var vector = loopbackLink1.getExpr();
        var loopbackLink = new LoopbackLink();
        loopbackLink.putFunction("LeastSquares", 2);
        loopbackLink.put(mt);
        loopbackLink.put(vector);
        var resExpr = loopbackLink.getExpr();
        var res = Utilities.evaluateExpr(resExpr);
        try
        {
            return new CustomArrayList<Double>(new Double[]{
                    res.part(new int[]{1}).asDouble(),
                    res.part(new int[]{2}).asDouble(),
                    res.part(new int[]{3}).asDouble(),
                    res.part(new int[]{4}).asDouble()
            });
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static ArrayList<Double> attachedToRoots(HashMap<EdgeVertex, Double> EdPR, HashMap<Object, Double> PR, String direction)
    {
        var data = new ArrayList<ArrayList<Double>>();
        BinaryFunction<WordVertex, WordVertex, EdgeVertex> EdFunc = (x, y) ->
        {
            var tail = new CustomArrayList<String>(new String[]{x.Word, x.Type});
            var head = new CustomArrayList<String>(new String[]{y.Word, y.Type});
            var edV = new EdgeVertex(tail, head);
            edV.Direction = x.Location < y.Location ? "next" : "before";
            return edV;
        };
        UnaryFunction<ArrayList<Object>, ArrayList<Double>> getRanks = (objs) ->
        {
            return Utilities.map((Object y) ->
            {
                if (y instanceof EdgeVertex)
                    return EdPR.get(y);
                else
                {
                    var origin = (WordVertex) y;
                    return PR.get(new CustomArrayList<String>(new String[]{origin.Word, origin.Type}));
                }
            }, objs);
        };
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            var roots = Utilities.select(g.vertexList(), (x) -> (g.vertexOutDegree(x) == 0));
            for (var root : roots)
            {
                var x = root;
                var inVs = Utilities.makeArrayList(g.inGoingVertices(root));
                Utilities.quickSort(inVs, (a, b) -> a.Location - b.Location);
                for (var i = 0; i <= inVs.size() - 2; i++)
                {
                    var iEle = inVs.get(i);
                    var nextIEle = inVs.get(i + 1);
                    WordVertex y, z;
                    if (direction.equals("left"))
                    {
                        y = iEle;
                        z = nextIEle;
                    } else
                    {
                        y = nextIEle;
                        z = iEle;
                    }
                    if (x.Word.equals(y.Word) || x.Word.equals(z.Word))
                        continue;
                    var yxEd = EdFunc.apply(y, x);
                    var zxEd = EdFunc.apply(z, x);
                    var ranks = getRanks.apply(
                            new CustomArrayList<Object>(new Object[]{x, yxEd, zxEd, y, z})
                    );
                    data.add(ranks);
                }
            }
        }
        Utilities.executeMathematicaCode("MyData=%0", data);
        var mt = new ArrayList<ArrayList<Double>>();
        var vector = new ArrayList<Double>();
        for (var tuple : data)
        {
            mt.add(Utilities.part(tuple, 0, 3));
            vector.add(tuple.get(4));
        }
        var mtExpr = Utilities.convertToExpr(mt);
        var vectorExpr = Utilities.convertToExpr(vector);
        var loopbackLink = new LoopbackLink();
        loopbackLink.putFunction("LeastSquares", 2);
        loopbackLink.put(mtExpr);
        loopbackLink.put(vectorExpr);
        var resExpr = Utilities.evaluateExpr(loopbackLink.getExpr());
        var res = new ArrayList<Double>();
        try
        {
            for (var i = 1; i <= resExpr.length(); i++)
                res.add(resExpr.part(new int[]{i}).asDouble());
            return res;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static ArrayList<Double> attachedToRoots(HashMap<EdgeVertex, Double> EdPR, HashMap<Object, Double> PR)
    {
        var data = new ArrayList<ArrayList<Double>>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            for (var v : g.vertexList())
            {
                if (toRootDistance(g, v) == 1)
                {
                    var vOuts = g.outGoingVertices(v);
                    var root = Utilities.getFirstElement(vOuts);
                    var direction = v.Location < root.Location ? "next" : "before";
                    var tail = new CustomArrayList<String>(new String[]{v.Word, v.Type});
                    var head = new CustomArrayList<String>(new String[]{root.Word, root.Type});
                    var edV = new EdgeVertex(tail, head);
                    edV.Direction = direction;
                    //trường hợp này có thể xảy ra nếu v.Word=root.Word
                    if (!EdPR.containsKey(edV))
                        continue;
                    var tuple = new CustomArrayList<Double>(new Double[]{
                            PR.get(head), EdPR.get(edV), PR.get(tail)
                    });
                    data.add(tuple);
                }
            }
        }
//        Utilities.executeMathematicaCode("MyData=%0",data);
        var loopbackLink0 = new LoopbackLink();
        loopbackLink0.putFunction("List", data.size());
        var loopbackLink1 = new LoopbackLink();
        loopbackLink1.putFunction("List", data.size());
        for (var tuple : data)
        {
            var a = tuple.get(0);
            var b = tuple.get(1);
            var c = tuple.get(2);
            loopbackLink0.putFunction("List", 2);
            loopbackLink0.put(a);
            loopbackLink0.put(b);
            loopbackLink1.put(c);
        }
        var mt = loopbackLink0.getExpr();
        var vector = loopbackLink1.getExpr();
        var loopbackLink = new LoopbackLink();
        loopbackLink.putFunction("LeastSquares", 2);
        loopbackLink.put(mt);
        loopbackLink.put(vector);
        var exprRes = loopbackLink.getExpr();
        exprRes = Utilities.evaluateExpr(exprRes);
        var res = new ArrayList<Double>();
        try
        {
            res.add(exprRes.part(new int[]{1}).asDouble());
            res.add(exprRes.part(new int[]{2}).asDouble());
            return res;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static int toRootDistance(Graph<WordVertex> g, WordVertex v)
    {
        var roots = Utilities.select(g.vertexList(),
                (x) -> g.vertexOutDegree(x) == 0);
        for (var root : roots)
        {
            var path = g.findPath(v, root);
            if (path != null)
                return path.size() - 1;
        }
        return -1;
    }

    public static ArrayList<Double> VertexToEdgeRankLeastSquaresNext = null;
    public static ArrayList<Double> VertexToEdgeRankLeastSquaresBefore = null;

    public static ArrayList<Double> vertexToEdgeRankLeastSquares(HashMap<EdgeVertex, Double> EdPR, HashMap<ArrayList<String>, Double> PR, String direction, AtomicReference<Double> variance)
    {
        if (direction.equals("next") && VertexToEdgeRankLeastSquaresNext != null)
            return VertexToEdgeRankLeastSquaresNext;
        if (direction.equals("before") && VertexToEdgeRankLeastSquaresBefore != null)
            return VertexToEdgeRankLeastSquaresBefore;

        var mt = new ArrayList<ArrayList<Double>>();
        var vt = new ArrayList<Double>();
        for (var edV : EdPR.keySet())
        {
            if (!edV.Direction.equals(direction))
                continue;
            var tail = edV.Tail;
            var head = edV.Head;
            var pair = new ArrayList<Double>();
            pair.add(PR.get(tail));
            pair.add(PR.get(head));
            mt.add(pair);
            vt.add(EdPR.get(edV));
        }
        var loopbackLink = new LoopbackLink();
        loopbackLink.putFunction("List", mt.size());
        for (var pair : mt)
        {
            loopbackLink.putFunction("List", 2);
            loopbackLink.put(pair.get(0));
            loopbackLink.put(pair.get(1));
        }
        var mtExpr = loopbackLink.getExpr();
        loopbackLink.clear();
        loopbackLink.putFunction("List", vt.size());
        for (var value : vt)
            loopbackLink.put(value);
        var vectorExpr = loopbackLink.getExpr();
        loopbackLink.clear();
        loopbackLink.putFunction("LeastSquares", 2);
        loopbackLink.put(mtExpr);
        loopbackLink.put(vectorExpr);
        var lSExpr = loopbackLink.getExpr();
        try
        {
            var res = Utilities.evaluateExpr(lSExpr);
            var mainRes = new CustomArrayList<Double>(new Double[]{
                    res.part(new int[]{1}).asDouble(),
                    res.part(new int[]{2}).asDouble()
            });
            if (variance != null)
            {
                var data = new ArrayList<ArrayList<Double>>();
                for (var i = 0; i <= mt.size() - 1; i++)
                {
                    var tuple = new CustomArrayList<Double>(new Double[]{mt.get(i).get(0), mt.get(i).get(1), vt.get(i)});
                    data.add(tuple);
                }
                variance.set(getLeastSquaresVariance(data, mainRes));
            }
            if (direction.equals("next"))
                VertexToEdgeRankLeastSquaresNext = mainRes;
            else VertexToEdgeRankLeastSquaresBefore = mainRes;
            return mainRes;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static ArrayList<Integer> rankDifference(HashMap<Object, Number> hm0, HashMap<Object, Number> hm1, Collection out)
    {
        var ks0 = Utilities.makeArrayList(hm0.keySet());
        Utilities.quickSort(ks0, (x, y) -> hm0.get(x).doubleValue() - hm0.get(y).doubleValue());
        var ks1 = Utilities.makeArrayList(hm1.keySet());
        Utilities.quickSort(ks1, (x, y) -> hm1.get(x).doubleValue() - hm1.get(y).doubleValue());
        var g = new Graph<>();
        for (var i = 0; i <= ks1.size() - 1; i++)
        {
            var iEle = ks1.get(i);
            var value = hm1.get(iEle);
            var selectedEles = Utilities.select(ks1, (x) -> hm1.get(x) == value);
            var aux = ks0.get(i);
            for (var ele : selectedEles)
            {
                g.addVertex(aux);
                g.addVertex(ele);
                g.addEdge(aux, ele);
            }
        }
//        Utilities.executeMathematicaCode("MyGraph=%0",g);
        var cycleLengths = new ArrayList<Integer>();
        for (var v : g.vertexList())
        {
            if (g.containsEdge(v, v))
                cycleLengths.add(1);
            else
            {
                var outVs = g.outGoingVertices(v);
                Integer shortestLength = null;
                for (var t : outVs)
                {
                    var gc = (Graph) g.clone();
                    gc.deleteEdge(v, t);
                    var path = gc.shortestPath(t, v);
                    if (out != null && path != null)
                    {
                        for (var i = 0; i <= path.size() - 1; i++)
                            out.add(path.get(i));
                    }
                    if (path != null)
                    {
                        var pathLength = path.size();
                        if (shortestLength == null)
                            shortestLength = pathLength;
                        else if (shortestLength.intValue() > pathLength)
                            shortestLength = pathLength;
                    }
                }
                cycleLengths.add(shortestLength);
            }
        }
        return cycleLengths;
    }

    public static Expr toEdgeRanks(HashMap<EdgeVertex, Double> EdPR)
    {
        var loopbackLink = new LoopbackLink();
        var ks = EdPR.keySet();
        var size = ks.size();
        loopbackLink.putFunction("Association", size);
        for (var ele : EdPR.keySet())
        {
            var tail = ele.Tail;
            var head = ele.Head;
            var direction = ele.Direction;
            loopbackLink.putFunction("Rule", 2);
            loopbackLink.putFunction("List", 3);
            loopbackLink.putFunction("List", 2);
            loopbackLink.put(new Expr(tail.get(0)));
            loopbackLink.put(new Expr(tail.get(1)));
            loopbackLink.putFunction("List", 2);
            loopbackLink.put(new Expr(head.get(0)));
            loopbackLink.put(new Expr(head.get(1)));
            loopbackLink.put(new Expr(direction));
            var value = ((Number) EdPR.get(ele)).doubleValue();
            loopbackLink.put(new Expr(value));
        }
        Utilities.executeMathematicaCode("PrintTemporary[\"Getting Expr\"]");
        return loopbackLink.getExpr();
    }

    public static Expr toVertexRank(HashMap<Object, Double> PR)
    {
        var loopbackLink = new LoopbackLink();
        var ks = PR.keySet();
        loopbackLink.putFunction("Association", ks.size());
        for (var ele : ks)
        {
            var value = PR.get(ele);
            var originEle = (ArrayList<String>) ele;
            var word = originEle.get(0);
            var type = originEle.get(1);
            loopbackLink.putFunction("Rule", 2);
            loopbackLink.putFunction("List", 2);
            loopbackLink.put(new Expr(word));
            loopbackLink.put(new Expr(type));
            loopbackLink.put(value);
        }
        Utilities.executeMathematicaCode("PrintTemporary@getting");
        return loopbackLink.getExpr();
    }

    public static <T> Graph<T> closestGraph(HashMap<T, ? extends Number> weights, UnaryFunction<T, String> typef)
    {
        var res = new Graph<T>();
        var kS = Utilities.makeArrayList(weights.keySet());
        var ksSize = kS.size();
        var pi = new ProgressIndicator(0, ksSize);
        pi.setDelay(1000);
        pi.show();
        for (var ele : kS)
            res.addVertex(ele);
        for (var i = 0; i <= ksSize - 1; i++)
        {
            if (pi.Stopped)
                break;
            pi.setValue(i);
            var ele0 = kS.get(i);
            var ele0type = typef.apply(ele0);
            var ele0Weight = weights.get(ele0);
            T closestEle = null;
            var currentDiff = -1d;
            for (var ele1 : kS)
            {
                if (ele0 == ele1)
                    continue;
                var ele1type = typef.apply(ele1);
                if (!ele0type.equals(ele1type))
                    continue;
                var ele1Weight = weights.get(ele1);
                var diff = Math.abs(ele1Weight.doubleValue() - ele0Weight.doubleValue());
                if (closestEle == null)
                {
                    closestEle = ele1;
                    currentDiff = diff;
                } else if (diff < currentDiff)
                {
                    closestEle = ele1;
                    currentDiff = diff;
                }
            }
            if (closestEle != null)
                res.addEdge(ele0, closestEle);
        }
        return res;
    }

    public static ArrayList<Double> nextVertexToEdgeRankLeastSquares = null;
    public static double nextVertexToEdgeRankLeastSquaresVariance;
    public static ArrayList<Double> beforeVertexToEdgeRankLeastSquares = null;
    public static double beforeVertexToEdgeRankLeastSquaresVariance;

    public static boolean isInitialized = false;
    public static ArrayList<ArrayList<ArrayList<String>>> Parsers = null;
    /**
     * cấu trúc là word->type0->type1->direction->frequency
     */
    public static HashMap<String, HashMap<String, HashMap<String, HashMap<String, Integer>>>> outWordDependence;
//    public static HashMap<String, HashMap<String, HashMap<String, HashMap<String, Integer>>>> inWordDependence;
    /**
     * cấu trúc là word->frequency
     */
    public static HashMap<String, Integer> totalAppearance;
    /**
     * cấu trúc là word->type->frequency
     */
    public static HashMap<String, HashMap<String, Integer>> WordAppearances = null;
    /**
     * type0->type1->direction->frequency
     */
    public static HashMap<String, HashMap<String, HashMap<String, Integer>>> typeDependency;
    /**
     * word->type->level->frequency
     */
    public static HashMap<String, HashMap<String, HashMap<Integer, Integer>>> levelAppearance;

    /**
     * cấu trúc là {type0,type1,type2}->{index0,index1,index2}->frequency
     */
    public static HashMap<String, HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>>> typeConnection;

    /**
     * cấu trúc là word->{type0,type1}->{index0,index1}->frequency
     * chú ý rằng trong cấu trúc các N sẽ được làm đơn giản hóa như Nc trở thành N
     */
    public static HashMap<String, HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>>> binaryCurveTypeConnection;

    public static HashMap<String, HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>>> ternaryCurveTypeConnection;

    public static HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>> curveTypeConnection;

    public static double curveTypeConnectionLimit;
    public static double appearanceLimit;

    private static CustomHashSet<String> people = new CustomHashSet<>(new String[]{
            "cô", "chú", "anh", "thím", "bác", "dì", "người", "con", "nàng"
    });

    //    public static ArrayList<Double> toRootLeastSquares = null;
//    public static ArrayList<Double> toNonRootLeastSquares = null;

    public static Graph<WordVertex> makeDependenceGraph(HashMap<EdgeVertex, Double> EdPR, HashMap<ArrayList<String>, Double> PR, ArrayList<String> sentence)
    {
        if (nextVertexToEdgeRankLeastSquares == null)
        {
            var nextVariance = new AtomicReference<Double>();
            nextVertexToEdgeRankLeastSquares = vertexToEdgeRankLeastSquares(EdPR, PR, "next", nextVariance);
            nextVertexToEdgeRankLeastSquaresVariance = nextVariance.get();

            var beforeVariance = new AtomicReference<Double>();
            beforeVertexToEdgeRankLeastSquares = vertexToEdgeRankLeastSquares(EdPR, PR, "before", beforeVariance);
            beforeVertexToEdgeRankLeastSquaresVariance = beforeVariance.get();
        }
        if (toFirstLevelLeastSquares == null)
            initializeToFirstLevelLeastSquares(EdPR, PR);
        if (toSecondLevelLeastSquares == null)
            initializeToSecondLevelLeastSquares(EdPR, PR);
        var res = new Graph<WordVertex>();
        var indexToTypes = new HashMap<Integer, Collection<String>>();
        for (var i = 0; i <= sentence.size() - 1; i++)
        {
            var iWord = sentence.get(i);
            if (!WordAppearances.containsKey(iWord))
                throw new RuntimeException("The word is not seen by the system");
            var aux = WordAppearances.get(iWord);
            indexToTypes.put(i, aux.keySet());
        }
        for (var i = 0; i <= sentence.size() - 1; i++)
        {
            var iWord = sentence.get(i);
            var iTypes = indexToTypes.get(i);
            for (var j = 0; j <= sentence.size() - 1; j++)
            {
                if (i == j)
                    continue;
                var direction = i < j ? "next" : "before";
                var jWord = sentence.get(j);
//                if (iWord.equals(jWord))
//                    continue;
                var jTypes = indexToTypes.get(j);
                for (var iType : iTypes)
                {
                    var iPair = new CustomArrayList<String>(new String[]{iWord, iType});
                    if (!PR.containsKey(iPair))
                        continue;
                    for (var jType : jTypes)
                    {
                        var jPair = new CustomArrayList<String>(new String[]{jWord, jType});
                        if (!PR.containsKey(jPair))
                            continue;
                        var edV = new EdgeVertex(iPair, jPair);
                        edV.Direction = direction;
                        double weight;
                        if (EdPR.containsKey(edV))
                        {
                            var weight0 = PR.get(iPair);
                            var weight1 = PR.get(jPair);
                            weight = EdPR.get(edV);
                            double idealWeight;
                            if (direction.equals("next"))
                                idealWeight = VietnameseAnalyzer.nextVertexToEdgeRankLeastSquares.get(0) * weight0 + VietnameseAnalyzer.nextVertexToEdgeRankLeastSquares.get(1) * weight1;
                            else
                                idealWeight = VietnameseAnalyzer.beforeVertexToEdgeRankLeastSquares.get(0) * weight0 + VietnameseAnalyzer.beforeVertexToEdgeRankLeastSquares.get(1) * weight1;
                            var aux = Math.abs(weight - idealWeight);
                            if (direction.equals("next"))
                            {
                                if (aux > nextVertexToEdgeRankLeastSquaresVariance)
                                {
                                    if (weight < idealWeight)
                                        weight = idealWeight - nextVertexToEdgeRankLeastSquaresVariance;
                                    else weight = idealWeight + nextVertexToEdgeRankLeastSquaresVariance;
                                }
                            } else
                            {
                                if (aux > beforeVertexToEdgeRankLeastSquaresVariance)
                                {
                                    if (weight < idealWeight)
                                        weight = idealWeight - beforeVertexToEdgeRankLeastSquaresVariance;
                                    else weight = idealWeight + beforeVertexToEdgeRankLeastSquaresVariance;
                                }
                            }
                        } else
                        {
                            var weight0 = PR.get(iPair);
                            var weight1 = PR.get(jPair);
                            if (direction.equals("next"))
                                weight = VietnameseAnalyzer.nextVertexToEdgeRankLeastSquares.get(0) * weight0 + VietnameseAnalyzer.nextVertexToEdgeRankLeastSquares.get(1) * weight1;
                            else
                                weight = VietnameseAnalyzer.beforeVertexToEdgeRankLeastSquares.get(0) * weight0 + VietnameseAnalyzer.beforeVertexToEdgeRankLeastSquares.get(1) * weight1;
                        }
                        {
                            var wordVertex0 = new WordVertex(i, iWord, iType);
                            var wordVertex1 = new WordVertex(j, jWord, jType);
                            res.addVertex(wordVertex0);
                            res.setVertexWeight(wordVertex0, PR.get(iPair));
                            res.addVertex(wordVertex1);
                            res.setVertexWeight(wordVertex1, PR.get(jPair));
                            res.addEdge(wordVertex0, wordVertex1);
                            res.setEdgeWeight(wordVertex0, wordVertex1, weight);
                            if (EdPR.containsKey(edV))
                                res.setEdgeProperty(wordVertex0, wordVertex1, "Directed", true);
                            else res.setEdgeProperty(wordVertex0, wordVertex1, "Directed", false);
                        }
                    }
                }
            }
        }
        return res;
    }

    public static ArrayList<ArrayList<String>> closestWord(HashMap<ArrayList<String>, Double> PR, ArrayList<String> wordInfo, Collection<ArrayList<String>> targets,
                                                           UnaryFunction<ArrayList<String>, Boolean> checkf, AtomicReference<Double> storedDiff)
    {
        if (!PR.containsKey(wordInfo))
            throw new RuntimeException("Invalid input");
        var value = PR.get(wordInfo).doubleValue();
        Double currentDiff = null;
        var res = new ArrayList<ArrayList<String>>();
        for (var word : targets)
        {
            if (!checkf.apply(word))
                continue;
            var wordType = word.get(1);
            var wordInfoType = wordInfo.get(1);
            if (!word.get(1).equals(wordInfo.get(1)) && !(wordType.startsWith("N") && wordInfoType.startsWith("N")))
                continue;
            var diff = Math.abs(PR.get(word).doubleValue() - value);
            if (currentDiff == null)
            {
                currentDiff = diff;
                res.add(word);
            } else if (diff == currentDiff.doubleValue())
            {
                res.add(word);
            } else if (diff < currentDiff.doubleValue())
            {
                currentDiff = diff;
                res.clear();
                res.add(word);
            }
        }
        if (res.contains(wordInfo))
        {
            res.clear();
            res.add(wordInfo);
        }
        storedDiff.set(currentDiff);
        return res;
    }

    public static HashMap<Object, Double> makePR(Expr expr)
    {
        try
        {
            var res = new HashMap<Object, Double>();
            var length = expr.length();
            for (var i = 1; i <= length; i++)
            {
                var value = expr.part(new int[]{i, 2}).asDouble();
                var word = expr.part(new int[]{i, 1, 1}).asString();
                var type = expr.part(new int[]{i, 1, 2}).asString();
                var key = new CustomArrayList<String>(new String[]{word, type});
                res.put(key, value);
            }
            return res;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static HashMap<EdgeVertex, Double> makeEdPR(Expr edgeRanks)
    {
        try
        {
            var res = new HashMap<EdgeVertex, Double>();
            var length = edgeRanks.length();
            var pi = new ProgressIndicator(0, length);
            pi.setDelay(1000);
            pi.show();
            for (var i = 1; i <= length; i++)
            {
                if (pi.Stopped)
                    break;
                pi.setValue(i);
                var iEle = edgeRanks.part(new int[]{i, 1});
//                if (iEle.stringQ())
//                {
//                    var sink = new EdgeVertex(null, null);
//                    sink.isSink = true;
//                    var value = edgeRanks.part(new int[]{i, 2}).asDouble();
//                    res.put(sink, value);
//                } else
//                {
                var tailWord = edgeRanks.part(new int[]{i, 1, 1, 1}).asString();
                var tailType = edgeRanks.part(new int[]{i, 1, 1, 2}).asString();
                var tail = new ArrayList<String>();
                tail.add(tailWord);
                tail.add(tailType);
                var headWord = edgeRanks.part(new int[]{i, 1, 2, 1}).asString();
                var headType = edgeRanks.part(new int[]{i, 1, 2, 2}).asString();
                var head = new ArrayList<String>();
                head.add(headWord);
                head.add(headType);
                var direction = edgeRanks.part(new int[]{i, 1, 3}).asString();
                var value = edgeRanks.part(new int[]{i, 2}).asDouble();
                var aux = new EdgeVertex(tail, head);
                aux.Direction = direction;
                res.put(aux, value);
//                }
            }
            return res;
        } catch (Exception e)
        {
            throw new RuntimeException("error");
        }
    }

    public static Graph<ArrayList<String>> getGraphUnion()
    {
        var res = new Graph<ArrayList<String>>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            var subRes = getGraphUnion(g);
            res.addVertices(subRes.vertexList());
            for (var ed : subRes.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
//                res.addVertex(v0);
//                res.addVertex(v1);
                var currentWeight = 0d;
                if (res.containsEdge(v0, v1))
                    currentWeight = res.getEdgeWeight(v0, v1);
                currentWeight += subRes.getEdgeWeight(ed);
                res.addEdge(v0, v1);
                res.setEdgeWeight(v0, v1, currentWeight);
            }
        }
        return res;
    }

    public static Graph<ArrayList<String>> getGraphUnion(Graph<WordVertex> g)
    {
        var res = new Graph<ArrayList<String>>();
        UnaryFunction<WordVertex, ArrayList<String>> func = (x) ->
        {
            var aux = new ArrayList<String>();
            aux.add(x.Word);
            aux.add(x.Type);
            return aux;
        };
        for (var v0 : g.vertexList())
        {
            var v00 = func.apply(v0);
            res.addVertex(v00);
            var outVs = g.outGoingVertices(v0);
            if (outVs.size() > 0)
            {
                for (var v1 : outVs)
                {
                    var v11 = func.apply(v1);
                    res.addVertex(v11);
                    var ar = new ArrayList<ArrayList<String>>();
                    ar.add(v00);
                    ar.add(v11);
                    var currentWeight = 0d;
                    if (res.containsEdge(v00, v11))
                        currentWeight = res.getEdgeWeight(v00, v11);
                    res.addEdge(ar);
                    res.setEdgeWeight(v00, v11, currentWeight + 1);
                }
            }
        }
        return res;
    }

    public static Graph<EdgeVertex> getEdgeConnectionGraph(Graph<WordVertex> g)
    {
        var res = new Graph<EdgeVertex>();
        UnaryFunction<WordVertex, ArrayList<String>> func = (w) ->
        {
            return new CustomArrayList<String>(new String[]{w.Word, w.Type});
        };
        for (var v : g.vertexList())
        {
            var v0 = func.apply(v);
            var inVs = g.inGoingVertices(v);
            var outVs = g.outGoingVertices(v);
            for (var s : inVs)
            {
                var sv = new ArrayList<WordVertex>();
                sv.add(s);
                sv.add(v);
                var s0 = func.apply(s);
                var V0 = new EdgeVertex(s0, v0);
                if (s.Location < v.Location)
                    V0.Direction = "next";
                else V0.Direction = "before";
                res.addVertex(V0);
                if (outVs.size() > 0)
                {
                    for (var t : outVs)
                    {
                        var vt = new ArrayList<WordVertex>();
                        vt.add(v);
                        vt.add(t);
                        var t0 = func.apply(t);
                        var V1 = new EdgeVertex(v0, t0);
                        if (v.Location < t.Location)
                            V1.Direction = "next";
                        else V1.Direction = "before";
                        res.addVertex(V1);
//                        if (!V0.equals(V1))
//                        {
                        var currentWeight = 0d;
                        if (res.containsEdge(V0, V1))
                            currentWeight = res.getEdgeWeight(V0, V1);
                        res.addEdge(V0, V1);
                        res.setEdgeWeight(V0, V1, currentWeight + 1);
//                        }
                    }
                }
            }
        }
        return res;
    }

    public static Graph<EdgeVertex> getEdgeConnectionGraph()
    {
        var res = new Graph<EdgeVertex>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            var subRes = getEdgeConnectionGraph(g);
            res.addVertices(subRes.vertexList());
            for (var ed : subRes.edgeList())
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                var edWeight = subRes.getEdgeWeight(v0, v1);
                var currentWeight = 0d;
                if (res.containsEdge(v0, v1))
                    currentWeight = res.getEdgeWeight(v0, v1);
                currentWeight += edWeight;
//                res.addVertex(v0);
//                res.addVertex(v1);
                res.addEdge(v0, v1);
                res.setEdgeWeight(v0, v1, currentWeight);
            }
        }
        return res;
    }

    public static HashSet<ArrayList<WordVertex>> getNonSuitableVertices(Graph<WordVertex> g)
    {
        var res = new HashSet<ArrayList<WordVertex>>();
        TernaryFunction<WordVertex, WordVertex, WordVertex, Boolean> isSuitableQ = (x, y, z) ->
        {
            return isTrivialCurveSuitableIndicesQ(x, y, z) && isBinaryCurveSuitableIndicesQ(x, y, z);
        };
        for (var v : g.vertexList())
        {
            var inVs = Utilities.makeArrayList(g.inGoingVertices(v));
            Utilities.naiveSort(inVs, (x, y) -> x.Location - y.Location);
            for (var i = 0; i <= inVs.size() - 2; i++)
            {
                var iEle = inVs.get(i);
                var nextIEle = inVs.get(i + 1);
                if (!isSuitableQ.apply(v, iEle, nextIEle))
                {
                    res.add(
                            new CustomArrayList<WordVertex>(new WordVertex[]{v, iEle, nextIEle})
                    );
                }
            }
            for (var i = 0; i <= inVs.size() - 3; i++)
            {
                var iEle = inVs.get(i);
                var nextIEle = inVs.get(i + 1);
                var nextNextIEle = inVs.get(i + 2);
                if (isSuitableQ.apply(v, iEle, nextIEle) && isSuitableQ.apply(v, nextIEle, nextNextIEle))
                    if (!isTernaryCurveSuitableIndicesQ(v, iEle, nextIEle, nextNextIEle))
                    {
                        res.add(new CustomArrayList<WordVertex>(
                                new WordVertex[]{v, iEle, nextIEle, nextNextIEle}
                        ));
                    }
            }
        }
        return res;
    }

    public static void getTernaryCurveTypeConnection()
    {
        ternaryCurveTypeConnection = new HashMap<>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            getCurveTypeConnection(g, 3, ternaryCurveTypeConnection);
        }
    }

    public static void getBinaryCurveTypeConnection()
    {
        binaryCurveTypeConnection = new HashMap<>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            getCurveTypeConnection(g, 2, binaryCurveTypeConnection);
        }
//        for (var word : binaryCurveTypeConnection.keySet())
//        {
//            var storedTypeses = Utilities.makeHashSet(binaryCurveTypeConnection.get(word).keySet());
//            for (var types : storedTypeses)
//            {
//                var type0 = types.get(0);
//                if (!type0.equals("E"))
//                    continue;
//                var type1 = types.get(1);
//                var type2 = types.get(2);
//                if (type1.startsWith("N") && type2.startsWith("N"))
//                {
//                    binaryCurveTypeConnection.get(word).remove(types);
//                }
//            }
//        }
    }

    private static final String $Failed = "$Failed";

    public static void getCurveTypeConnection(Graph<WordVertex> g, int length, HashMap out)
    {
        UnaryFunction<String, String> toN = (x) ->
        {
            if (x.startsWith("N"))
                return "N";
            else return x;
        };
        var vs = g.vertexList();
        for (var v : vs)
        {
            var inVs = Utilities.makeArrayList(g.inGoingVertices(v));
            Utilities.quickSort(inVs,
                    (x, y) -> x.Location - y.Location
            );
            if (0 < inVs.size() && inVs.size() < length)
            {
                var types = new ArrayList<String>();
                types.add(toN.apply(v.Type));
                var indices = new ArrayList<Integer>();
                indices.add(v.Location);
                for (var i = 0; i <= inVs.size() - 1; i++)
                {
                    var iEle = inVs.get(i);
                    types.add(toN.apply(iEle.Type));
                    indices.add(iEle.Location);
                }
                indices = simplifyIndices(indices);
                var currentValue = 0;
                if (keySequenceExistsQ(out, v.Word, types, indices))
                    currentValue = (Integer) getValue(out, v.Word, types, indices);
                insertValue(out, new Object[]{v.Word, types, indices}, currentValue + 1);
            }
            for (var i = 0; i <= inVs.size() - length; i++)
            {
                var indices = new ArrayList<Integer>();
                indices.add(v.Location);
                var types = new ArrayList<String>();
                types.add(toN.apply(v.Type));
                for (var j = 0; j <= length - 1; j++)
                {
                    var jV = inVs.get(i + j);
                    indices.add(jV.Location);
                    types.add(toN.apply(jV.Type));
                }
                indices = simplifyIndices(indices);
                var word = v.Word;
                if (!keySequenceExistsQ(out, word, types, indices))
                    insertValue(out, new Object[]{word, types, indices}, 0);
                var value = (Integer) getValue(out, word, types, indices);
                insertValue(out, new Object[]{word, types, indices}, value + 1);
            }
        }
    }

//    public static double getTypeConnectionLimit()
//    {
//        var values = new ArrayList<Double>();
//        for (var word : typeConnection.keySet())
//            for (var types : typeConnection.get(word).keySet())
//            {
//                var auxValues = (ArrayList<Integer>) (Object) getLeafValues(typeConnection.get(word).get(types));
//                values.add(Utilities.sum(auxValues));
//            }
//        var mean = Utilities.mean(values);
//        var variance = Utilities.variance(values);
//        return mean + variance;
//    }

    public static double getCurveTypeConnectionLimit()
    {
        var values = new ArrayList<Double>();
        for (var types : curveTypeConnection.keySet())
        {
            var auxValues = (ArrayList<Integer>) (Object) getLeafValues(curveTypeConnection.get(types));
            values.add(Utilities.sum(auxValues));
        }
        var mean = Utilities.mean(values);
        var variance = Utilities.variance(values);
        return mean + variance;
    }

    public static ArrayList<Object> getLeafValues(Object obj)
    {
        var res = new ArrayList<Object>();
        if (!(obj instanceof HashMap))
            res.add(obj);
        else
        {
            var origin = (HashMap) obj;
            for (var key : origin.keySet())
            {
                var subRes = getLeafValues(origin.get(key));
                res.addAll(subRes);
            }
        }
        return res;
    }

    public static void getCurveTypeConnection()
    {
        curveTypeConnection = new HashMap<>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            var con = getCurveTypeConnection(g);
            for (var types : con.keySet())
                for (var indices : con.get(types).keySet())
                {
                    var value = con.get(types).get(indices);
                    if (!keySequenceExistsQ(curveTypeConnection, types, indices))
                        insertValue(curveTypeConnection, new Object[]{types, indices}, 0);
                    var eValue = (Integer) getValue(curveTypeConnection, types, indices);
                    insertValue(curveTypeConnection, new Object[]{types, indices}, value + eValue);
                }
        }
    }

    /**
     * hàm này dành cho trivial tức là không phân biệt các từ
     *
     * @param g
     * @return
     */
    public static HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>> getCurveTypeConnection(Graph<WordVertex> g)
    {
        var res = new HashMap<ArrayList<String>, HashMap<ArrayList<Integer>, Integer>>();
        for (var v : g.getVertices())
        {
            var inVs = Utilities.makeArrayList(g.inGoingVertices(v));
            Utilities.quickSort(inVs,
                    (x, y) -> x.Location - y.Location
            );
            for (var i = 0; i <= inVs.size() - 2; i++)
            {
                var iEle = inVs.get(i);
                var nextIEle = inVs.get(i + 1);
                var types = new CustomArrayList<String>(new String[]{
                        v.Type, iEle.Type, nextIEle.Type
                });
                ArrayList<Integer> indices = new CustomArrayList<Integer>(new Integer[]{
                        v.Location, iEle.Location, nextIEle.Location
                });
                indices = simplifyIndices(indices);
                if (!keySequenceExistsQ(res, types, indices))
                    insertValue(res, new Object[]{types, indices}, 0);
                var value = (Integer) getValue(res, types, indices);
                insertValue(res, new Object[]{types, indices}, value + 1);
            }
        }
        return res;
    }

//    public static double getTypeConnectionVariance()
//    {
//        var mean = getTypeConnectionMean();
//        var res = 0d;
//        int count = 0;
//        for (var type : typeConnection.keySet())
//            for (var indices : typeConnection.get(type).keySet())
//            {
//                var value = typeConnection.get(type).get(indices);
//                res += (value - mean) * (value - mean);
//                count++;
//            }
//        res = res / count;
//        return Math.sqrt(res);
//    }

//    public static double getTypeConnectionMean()
//    {
//        double res = 0;
//        int count = 0;
//        for (var type : typeConnection.keySet())
//            for (var indices : typeConnection.get(type).keySet())
//            {
//                res += typeConnection.get(type).get(indices);
//                count++;
//            }
//        return res / count;
//    }

    public static Graph<WordVertex> getSubgraph(Graph<WordVertex> g, HashMap<String, String> typef)
    {
        var resg = (Graph<WordVertex>) g.clone();
        var vs = g.getVertices();
        var keptVs = Utilities.select(vs,
                (v) ->
                {
                    var word = v.Word;
                    var type = v.Type;
                    return typef.containsKey(word) && type.equals(typef.get(word));
                }
        );
        var deletedVs = Utilities.complement(vs, keptVs);
        Utilities.map((WordVertex x) ->
        {
            resg.deleteVertex(x);
        }, deletedVs);
        return resg;
    }

    public static HashMap<String, HashMap<String, Object>> Options;

    /*public static HashMap<String,NullAction> InitializedActions=new HashMap<>();*/
    public static void initializeOptions()
    {
        Options = new HashMap<>();
        insertValue(Options, new Object[]{"maximumSpanningTree", "startingEdges"}, new HashSet<>());
        insertValue(Options, new Object[]{"maximumSpanningTree", "checkingWord"}, null);
        insertValue(Options, new Object[]{"maximumSpanningTree", "cycleDetection"}, true);
    }

    public static Graph<WordVertex> maximumSpanningTree(Graph<WordVertex> g, WordVertex root)
    {
        return maximumSpanningTree(g, root, new HashMap<>());
    }

    private static final HashSet<ArrayList<String>> waitingWords = new CustomHashSet<ArrayList<String>>(
            new ArrayList[]{
                    new CustomArrayList<String>(new String[]{"cái", "Nc"}),
                    new CustomArrayList<String>(new String[]{"người", "Nc"}),
                    new CustomArrayList<String>(new String[]{"là", "V"})
            }
    );

    public static <T> T findQuickMinimal(Collection<T> col, BinaryFunction<T, T, ? extends Number> comparator)
    {
        T res = null;
        for (var ele : col)
            if (res == null)
                res = ele;
            else if (comparator.apply(ele, res).doubleValue() < 0)
                res = ele;
        return res;
    }

    public static ArrayList<WordVertex> getSortedErrorWordVertices(Graph<WordVertex> tree)
    {
        var errors = countErrors(tree);
        var eASs = getErrorAppearanceStatics();
        var propertyNames = Utilities.makeArrayList(eASs.keySet());
        Utilities.sortBy(propertyNames, x -> eASs.get(x));
        var errorG = new Graph<Object>();
        for (var i = 0; i <= propertyNames.size() - 1; i++)
        {
            var errorSet = (Collection) errors.get(propertyNames.get(i));
            Integer index = i;
            Utilities.map(x ->
            {
                errorG.addEdge(index, x);
            }, errorSet);
        }
        var res = Utilities.makeArrayList(tree.edgeList());
        Utilities.quickSort(res,
                (ed0, ed1) ->
                {
                    var errorIndices0 = new ArrayList<Integer>();
                    Utilities.map(
                            x ->
                            {
                                if (errorG.containsVertex(x))
                                    errorIndices0.addAll((HashSet<Integer>) (Object) errorG.inGoingVertices(x));
                            },
                            new Object[]{ed0.get(0), ed0.get(1), ed0}
                    );
                    Utilities.sortBy(errorIndices0, x -> x);
                    var errorIndices1 = new ArrayList<Integer>();
                    Utilities.map(
                            x ->
                            {
                                if (errorG.containsVertex(x))
                                    errorIndices1.addAll((HashSet<Integer>) (Object) errorG.inGoingVertices(x));
                            },
                            new Object[]{ed1.get(0), ed1.get(1), ed1}
                    );
                    Utilities.sortBy(errorIndices1, x -> x);
                    var size0 = errorIndices0.size();
                    var size1 = errorIndices1.size();
                    var minSize = Utilities.min(size0, size1);
                    var padding0 = Utilities.table(x -> propertyNames.size()
                            , 0, size0 - minSize - 1
                    );
                    var padding1 = Utilities.table(x -> propertyNames.size()
                            , 0, size1 - minSize - 1
                    );
                    return Utilities.lexicographicOrder(
                            Utilities.join(errorIndices0, padding0),
                            Utilities.join(errorIndices1, padding1), (x, y) -> x - y
                    );
                }
        );
        return Utilities.deleteDuplicates(Utilities.map((ArrayList<WordVertex> x) -> x.get(0), res),
                (x, y) -> x.equals(y)
        );
//        for (var name : propertyNames)
//        {
//            var errorSet = (Collection) errors.get(name);
//            Utilities.map(x ->
//            {
//                if (x instanceof ArrayList)
//                    res.add(((ArrayList<WordVertex>) x).get(0));
//                if (x instanceof WordVertex)
//                {
//                    res.add((WordVertex) x);
//                    res.addAll(tree.inGoingVertices((WordVertex) x));
//                }
//            }, errorSet);
//        }
//        return Utilities.deleteDuplicates(res, (x, y) -> x.equals(y));
    }

    public static Graph<WordVertex> maximumSpanningTree(Graph<WordVertex> g, WordVertex root, HashMap<String, Object> options)
    {
        HashSet<ArrayList<WordVertex>> startingEdges;
        final var startingEdgesStr = "startingEdges";
        if (options.containsKey(startingEdgesStr))
            startingEdges = (HashSet) options.get(startingEdgesStr);
        else startingEdges = new HashSet<>();
        HashSet<ArrayList<WordVertex>> currentEds = new HashSet<>();
        currentEds.addAll(startingEdges);
        var eds = g.getEdges();
        while (true)
        {
            var rootInvs = NullFunction.createInstance(() ->
            {
                var auxg = new Graph<WordVertex>(g.vertexList(), currentEds);
                return auxg.vertexInComponent(root);
            }).apply();
            var chosenEds = Utilities.select(eds,
                    (ArrayList<WordVertex> ed) ->
                    {
                        var x = ed.get(0);
                        var y = ed.get(1);
                        var check0 = rootInvs.contains(y) && !rootInvs.contains(x);
                        if (!check0)
                            return false;
                        var auxg = new Graph<WordVertex>(Utilities.append(currentEds, ed));
                        return Utilities.allTrue(auxg.vertexList(),
                                z -> auxg.vertexOutDegree(z) <= 1
                        );
                    }
            );
            if (chosenEds.size() == 0)
                break;
            var chosenEd = findQuickMinimal(chosenEds,
                    (ed0, ed1) -> orderingf(g, ed0, ed1, currentEds,
                            NullFunction.createInstance(() ->
                            {
                                var aux = (HashMap<String, Object>) options.clone();
                                aux.put("IgnoreErrors", true);
                                return aux;
                            }).apply()
                    )
            );
            currentEds.add(chosenEd);
        }
        while (true)
        {
            var metQ = false;
            var currentVs = NullFunction.createInstance(() ->
            {
                var aux = new HashSet<WordVertex>();
                Utilities.map(
                        x ->
                        {
                            aux.addAll(x);
                        }, currentEds);
                return aux;
            }).apply();
            var sortedCurrentVs = NullFunction.createInstance(() ->
            {
                var auxg = new Graph<WordVertex>(currentVs, currentEds);
                var auxRes = getSortedErrorWordVertices(auxg);
                var subAuxg = auxg.subgraph(
                        Utilities.complement(currentVs, auxRes)
                );
                return Utilities.join(auxRes, Utilities.topologicalSort(subAuxg));
            }).apply();
            for (var v : sortedCurrentVs)
            {
                if (v.equals(root))
                    continue;
                var auxg = new Graph<WordVertex>(currentVs, currentEds);
                var inCompos = auxg.vertexInComponent(v);
                var inComposEds = Utilities.select(currentEds,
                        (ArrayList<WordVertex> ed) ->
                        {
                            var x = ed.get(0);
                            var y = ed.get(1);
                            return inCompos.contains(x) && inCompos.contains(y);
                        }
                );
                var otherVertices = Utilities.complement(currentVs, inCompos);
                final var otherEds = Utilities.makeHashSet(Utilities.select(currentEds,
                        (ArrayList<WordVertex> ed) ->
                        {
                            var x = ed.get(0);
                            var y = ed.get(1);
                            return otherVertices.contains(x) && otherVertices.contains(y);
                        }
                ));
                var auxEd = Utilities.firstCase(currentEds,
                        (ed) -> ed.get(0).equals(v), (ArrayList<WordVertex>) null
                );
                if (auxEd == null)
                    continue;
                var chosenEds = Utilities.select(eds,
                        (ArrayList<WordVertex> ed) ->
                        {
                            var x = ed.get(0);
                            var y = ed.get(1);
                            var check0 = x.equals(v);
                            var check1 = otherVertices.contains(y);
                            return check0 && check1;
                        }
                );
                if (chosenEds.size() == 0)
                    continue;
                final var remainedEds = Utilities.makeHashSet(Utilities.join(inComposEds, otherEds));
                var chosenEd = findQuickMinimal(chosenEds,
                        (ed0, ed1) -> orderingf(g, ed0, ed1, remainedEds, options)
                );
                if (orderingf(g, chosenEd, auxEd, remainedEds, options) == 0)
                    continue;
                else
                {
                    currentEds.remove(auxEd);
                    currentEds.add(chosenEd);
                    metQ = true;
                    break;
                }
            }
            if (!metQ)
                break;
        }
        var res = new Graph<WordVertex>(currentEds);
        if (currentEds.size() == 0)
            res.addVertex(root);
        res = findABetterParser(g, res);
        return res;
    }

    //    private static boolean needToShow = false;
    public static double typeConnectionLimit;

    private static boolean isMatchQ(ArrayList<String> typeC, ArrayList<String> pat)
    {
        if (pat.size() != typeC.size())
            return false;
        for (var i = 0; i <= pat.size() - 1; i++)
        {
            var iPat = pat.get(i);
            if (iPat == null)
                continue;
            if (!iPat.equals(typeC.get(i)))
                return false;
        }
        return true;
    }

    public static boolean checkForbiddenTypeConnection(Graph<WordVertex> g, WordVertex v/*, HashSet<ArrayList<String>> forbiddens*/)
    {
        var lengths = new HashSet<Integer>();
        for (var ar : forbiddenTypeConnections)
            lengths.add(ar.size() - 1);
        for (var length : lengths)
        {
            var typeC = auxGetTypeConnection(g, v, length);
            if (typeC != null)
            {
                if (Utilities.anyTrue(forbiddenTypeConnections, (x) -> isMatchQ(typeC, x)))
                    return false;
            }
        }
        return true;
    }

    private static ArrayList<String> auxGetTypeConnection(Graph<WordVertex> g, WordVertex v)
    {
        return auxGetTypeConnection(g, v, 2);
    }

    private static ArrayList<String> auxGetTypeConnection(Graph<WordVertex> g, WordVertex v, int length)
    {
        try
        {
            var res = new ArrayList<String>();
            var runningV = v;
            for (var i = 0; i <= length; i++)
            {
                res.add(runningV.Type);
                var outVs = g.outGoingVertices(runningV);
                runningV = Utilities.getFirstElement(outVs);
            }
            return res;
        } catch (Exception e)
        {
            return null;
        }
    }

    public static boolean typeConectionCheck(Graph<WordVertex> g, ArrayList<WordVertex> ed, AtomicReference<String> info)
    {
        var u = ed.get(0);
        var v = ed.get(1);
        var inUVs = g.inGoingVertices(u);
        for (var s : inUVs)
        {
            var check = isTypeConnectionSuitableIndicesQ(s, u, v);
            if (!check)
            {
                info.set(s.toString() + "," + u + "," + v);
                return false;
            }
        }
        var outVVs = g.outGoingVertices(v);
        for (var s : outVVs)
        {
            var check = isTypeConnectionSuitableIndicesQ(u, v, s);
            if (!check)
            {
                info.set(u.toString() + "," + v + "," + s);
                return false;
            }
        }
        return true;
    }

    public static boolean isTernaryCurveSuitableIndicesQ(WordVertex a, WordVertex b, WordVertex c, WordVertex d)
    {
        var ratio = 1d / 5;
        var word = a.Word;
        if (ternaryCurveTypeConnection.containsKey(word) && totalAppearance.get(word) >= appearanceLimit)
        {
            var values = (ArrayList<Integer>) (Object) getLeafValues(ternaryCurveTypeConnection.get(word));
            var max = Utilities.max(values, (x, y) -> x - y);
            var types = Utilities.map((x) -> x.Type,
                    new CustomArrayList<WordVertex>(new WordVertex[]{a, b, c, d})
            );
            var indices = Utilities.map((x) -> x.Location,
                    new CustomArrayList<WordVertex>(new WordVertex[]{a, b, c, d})
            );
            indices = simplifyIndices(indices);
            if (keySequenceExistsQ(ternaryCurveTypeConnection, word, types, indices))
            {
                var value = (Integer) getValue(ternaryCurveTypeConnection, word, types, indices);
                return value >= ratio * max;
            } else return false;
        } else return true;
    }

    public static boolean curveTypeConnectionCheck(Graph<WordVertex> g, ArrayList<WordVertex> ed, AtomicReference<String> info)
    {
        var u = ed.get(0);
        var v = ed.get(1);
        var inVs = Utilities.makeArrayList(g.inGoingVertices(v));
        Utilities.quickSort(inVs, (x, y) -> x.Location - y.Location);

        {
            for (var i = 0; i <= inVs.size() - 2; i++)
            {
                var iEle = inVs.get(i);
                var nextIEle = inVs.get(i + 1);
                if (u.equals(iEle) || u.equals(nextIEle))
                {
                    if (!isBinaryCurveSuitableIndicesQ(v, iEle, nextIEle))
                    {
                        info.set("Binary:" + v + "," + iEle + "," + nextIEle);
                        return false;
                    }
                }
            }
        }
        return true;
    }

    public static boolean isLaCorrectConnection(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        var u = ed.get(0);
        if (!(u.Type.equals("V") && u.Word.equals("là")))
            return true;
        var v = ed.get(1);
        var toRoots = new ArrayList<WordVertex>();
        var runningV = v;
        while (true)
        {
            toRoots.add(runningV);
            var outVs = g.outGoingVertices(runningV);
            if (outVs.size() == 0)
                break;
            else runningV = Utilities.getFirstElement(outVs);
        }
        var c = Utilities.count(toRoots,
                (x) -> x.Type.startsWith("N")
        );
        return c < 2;
    }

    public static boolean isCorrectEIndices(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        var u = ed.get(0);
        var v = ed.get(1);
        if (!v.Type.equals("E"))
            return true;
        var uInvs = g.vertexInComponent(u);
        uInvs.remove(u);
        if (uInvs.size() == 0)
            return true;
        else
        {
            var indices = Utilities.map((WordVertex x) -> x.Location, uInvs);
            var diffs = Utilities.map(
                    (Integer x) -> x - u.Location, indices
            );
            return diffs.contains(1);
        }
    }

    private static ArrayList<WordVertex> outGoingPath(Graph<WordVertex> g, WordVertex v, UnaryFunction<ArrayList<WordVertex>, Boolean> checkf)
    {
        var res = new ArrayList<WordVertex>();
        var runningV = v;
        while (true)
        {
            var auxRes = Utilities.append(res, runningV);
            if (!checkf.apply(auxRes))
                break;
            else
            {
                res.add(runningV);
                var outVs = g.outGoingVertices(runningV);
                if (outVs.size() == 0)
                    break;
                else runningV = Utilities.getFirstElement(outVs);
            }
        }
        return res;
    }

    private static HashSet<String> ENConnectionWords = new CustomHashSet<String>(
            new String[]{"ở", "từ", "với", "để", "bằng", "của"}
    );

    public static boolean isCorrectEConnection(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        var u = ed.get(0);
        if (!u.Type.equals("E"))
            return true;
        if (!ENConnectionWords.contains(u.Word))
            return true;
        var uWord = u.Word;
        if (totalAppearance.get(uWord) < appearanceLimit)
            return true;
        var v = ed.get(1);
        var outVs = g.outGoingVertices(v);
        if (outVs.size() == 0)
            return true;
        var outV = Utilities.getFirstElement(outVs);
        var outVPath = outGoingPath(g, outV,
                (ArrayList<WordVertex> path) ->
                {
                    return Utilities.allTrue(path,
                            (x) -> !((x.Type.equals("E")) || (x.Type.equals("V") && x.Word.equals("là")))
                    );
                }
        );
        return !Utilities.anyTrue(outVPath,
                (x) -> x.Type.startsWith("N")
        );
    }

    public static HashMap<ArrayList<WordVertex>, Double> getEdgeWeights(Graph<WordVertex> g, Graph<WordVertex> tree)
    {
        var res = new HashMap<ArrayList<WordVertex>, Double>();
        for (var ed : tree.edgeList())
            res.put(ed, g.getEdgeWeight(ed));
        return res;
    }

    public static HashMap<ArrayList<WordVertex>, Double> getEdgeRanks(Graph<WordVertex> tree)
    {
        var eC = getEdgeConnectionGraph(tree);
        var opts = new HashMap<String, Object>();
        opts.put("Show Progress", false);
        opts.put("Step Number", 100);
        opts.put("Damping Factor", 0.85d);
        var edRs = Graph.pageRank(eC, opts);
        var res = new HashMap<ArrayList<WordVertex>, Double>();
        UnaryFunction<WordVertex, ArrayList> func = (x) ->
        {
            var aux = new ArrayList<String>();
            aux.add(x.Word);
            aux.add(x.Type);
            return aux;
        };
        for (var ed : tree.edgeList())
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            var direction = v0.Location < v1.Location ? "next" : "before";
            var edgeVertex = new EdgeVertex(func.apply(v0), func.apply(v1));
            edgeVertex.Direction = direction;
            res.put(ed, edRs.get(edgeVertex));
        }
        return res;
    }

    public static int rankDifference(Graph<WordVertex> g, Graph<WordVertex> tree, Collection out)
    {
        var hm0 = getEdgeWeights(g, tree);
        var hm1 = getEdgeRanks(tree);
        var lengths = rankDifference((HashMap<Object, Number>) (Object) hm0, (HashMap<Object, Number>) (Object) hm1, out);
        return Utilities.max(lengths, (x, y) -> x - y);
    }

    public static HashSet<ArrayList<String>> forbiddenTypeConnections;

    public static boolean distanceCheck(Graph<WordVertex> g, ArrayList<WordVertex> ed, String type)
    {
        var v0 = ed.get(0);
        var v1 = ed.get(1);
        if (v0.Type.equals(type) && v1.Type.equals(type))
        {
            var inVs = g.vertexInComponent(v0);
            var dists = Utilities.map((WordVertex x) -> Math.abs(x.Location - v1.Location), inVs);
            var minDist = Utilities.min(dists, (x, y) -> x - y);
            return minDist.intValue() == 1;
        } else return true;
    }

    public static boolean VDistanceCheck(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        return distanceCheck(g, ed, "V");
    }

    public static boolean NDistanceCheck(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        return distanceCheck(g, ed, "N");
    }

    public static HashMap<EdgeVertex, Double> makeEdPRFromGraph(Graph<WordVertex> g)
    {
        UnaryFunction<ArrayList<WordVertex>, EdgeVertex> getEdgeVertex = (ed) ->
        {
            var v0 = ed.get(0);
            var v1 = ed.get(1);
            var res = new EdgeVertex(new CustomArrayList<String>(new String[]{v0.Word, v0.Type}),
                    new CustomArrayList<String>(new String[]{v1.Word, v1.Type})
            );
            res.Direction = v0.Location < v1.Location ? "next" : "before";
            return res;
        };
        var res = new HashMap<EdgeVertex, Double>();
        for (var ed : g.edgeList())
            res.put(getEdgeVertex.apply(ed), g.getEdgeWeight(ed));
        return res;
    }

    public static HashMap<ArrayList<String>, Double> makePRFromGraph(Graph<WordVertex> g)
    {
        var res = new HashMap<ArrayList<String>, Double>();
        for (var v : g.vertexList())
            res.put(new CustomArrayList<String>(new String[]{v.Word, v.Type}), g.getVertexWeight(v));
        return res;
    }

    private static Graph<WordVertex> getLocal(Graph<WordVertex> tree, WordVertex targetV)
    {
        var allVs = new HashSet<WordVertex>();
        var interchange = Utilities.getFirstElement(tree.outGoingVertices(targetV));
        var inVs = tree.inGoingVertices(interchange);
        var lefts = Utilities.select(inVs,
                (v) -> v.Location < targetV.Location
        );
        Utilities.quickSort(lefts, (x, y) -> x.Location - y.Location);
        var rights = Utilities.select(inVs,
                (v) -> v.Location > targetV.Location
        );
        Utilities.quickSort(rights, (x, y) -> x.Location - y.Location);
        allVs.add(interchange);
        var intOutVs = tree.outGoingVertices(interchange);
        if (intOutVs.size() > 0)
            allVs.add(Utilities.getFirstElement(intOutVs));
        if (lefts.size() > 0)
            allVs.add(Utilities.getLastElement(lefts));
        if (rights.size() > 0)
            allVs.add(Utilities.getFirstElement(rights));
        allVs.add(targetV);
        return tree.subgraph(allVs);
    }

    /**
     * ý tưởng này hoạt động không tốt
     *
     * @param g
     * @param tree
     * @return
     */
    public static double leastSquaresDiff(Graph<WordVertex> g, Graph<WordVertex> tree)
    {
        var res = 0d;
        for (var ed : tree.edgeList())
        {
            var diff = leastSquaresDiff(g, tree, ed);
            res += (diff * diff);
        }
        return res;
    }

    private static double leastSquaresDiff(Graph<WordVertex> g, Graph<WordVertex> tree, ArrayList<WordVertex> ed)
    {
        var gEdPR = makeEdPRFromGraph(g);
        var gPR = makePRFromGraph(g);
        var v = ed.get(0);
        var localg = getLocal(tree, v);
        var borders = Utilities.select(localg.vertexList(),
                (w) -> localg.vertexInDegree(w) == 0
        );
        Utilities.quickSort(borders, (x, y) -> x.Location - y.Location);
        var root = Utilities.getFirstElement(Utilities.select(localg.vertexList(),
                (w) -> localg.vertexOutDegree(w) == 0
        ));
        var path = localg.findPath(v, root);
        var length = path.size() - 1;
        var pos = Utilities.firstPosition(borders,
                (w) -> w.equals(v)
        );
        var tuple = getTuple(gEdPR, gPR, localg, v);
        BinaryFunction<ArrayList<Double>, ArrayList<Double>, Double> computeDiff = (leastSquares, x) ->
        {
            var size = leastSquares.size();
            var sum = 0d;
            for (var i = 0; i <= size - 1; i++)
                sum += leastSquares.get(i) * x.get(i);
            var lastValue = x.get(size);
            return Math.abs(lastValue - sum);
        };
        if (length == 1)
        {
            switch (borders.size())
            {
                case 1:
                    return computeDiff.apply(toFirstLevelLeastSquares.Single, tuple);
                case 2:
                    switch (pos)
                    {
                        case 0:
                            return computeDiff.apply(toFirstLevelLeastSquares.Left, tuple);
                        case 1:
                            return computeDiff.apply(toFirstLevelLeastSquares.Right, tuple);
                    }
                    break;
                case 3:
                    return computeDiff.apply(toFirstLevelLeastSquares.Between, tuple);
            }
        } else
        {
            switch (borders.size())
            {
                case 1:
                    return computeDiff.apply(toSecondLevelLeastSquares.Single, tuple);
                case 2:
                    switch (pos)
                    {
                        case 0:
                            return computeDiff.apply(toSecondLevelLeastSquares.Left, tuple);
                        case 1:
                            return computeDiff.apply(toSecondLevelLeastSquares.Right, tuple);
                    }
                    break;
                case 3:
                    return computeDiff.apply(toSecondLevelLeastSquares.Between, tuple);
            }
        }
        throw new RuntimeException("leastSquareDiff unexpected return");
    }

    public static double getTypePairDirectionMean(String direction)
    {
        var data = new ArrayList<Double>();
        for (var pair : typePairDirections.keySet())
        {
            var corres = typePairDirections.get(pair);
            if (corres.containsKey(direction))
                data.add(corres.get(direction).doubleValue());
            else data.add(0d);
        }
        return Utilities.mean(data);
    }

    public static boolean isCorrectTypePairDirection(ArrayList<WordVertex> ed)
    {
        if (typePairDirectionLeastSquares == null)
            initializeTypePairDirectionLeastSquares();
        var v0 = ed.get(0);
        var v1 = ed.get(1);
        UnaryFunction<String, String> simplifyN = (x) ->
        {
            if (x.startsWith("N"))
                return "N";
            else return x;
        };
        var typePair = new CustomArrayList<String>(new String[]{
                simplifyN.apply(v0.Type), simplifyN.apply(v1.Type)
        });
        var nextMean = getTypePairDirectionMean("next");
        var beforeMean = getTypePairDirectionMean("before");
        if (typePairDirections.containsKey(typePair))
        {
            final var ratio = 1d;
            var nextValue = (double) typePairDirections.get(typePair).get("next");
            var beforeValue = (double) typePairDirections.get(typePair).get("before");

            if (beforeValue > ratio * nextValue * typePairDirectionLeastSquares.doubleValue())
                if (v0.Location < v1.Location)
                {
                    if (nextValue > nextMean)
                        return true;
                    return false;
                }

            if (nextValue > ratio * beforeValue * typePairDirectionLeastSquares.doubleValue())
                if (v0.Location > v1.Location)
                {
                    if (beforeValue > beforeMean)
                        return true;
                    else return false;
                }
        } else return false;
        return true;
    }

    public static boolean isVNCorrect(Graph<WordVertex> tree, ArrayList<WordVertex> ed)
    {
        UnaryFunction<WordVertex, Boolean> isNoun = (x) ->
        {
            return x.Type.startsWith("N") || x.Type.equals("P");
        };
        var v0 = ed.get(0);
        var v1 = ed.get(1);
//        if (v1.isRangMarked)
//            return true;
        return !(v0.Location < v1.Location && isNoun.apply(v0) && v1.Type.equals("V") && tree.vertexOutDegree(v1) != 0);
    }

    public static boolean isSensibleEdge(ArrayList<WordVertex> ed)
    {
        if (typePairDirectionLeastSquares == null)
            initializeTypePairDirectionLeastSquares();
        if (!isCorrectTypePairDirection(ed))
            return false;
        return true;
    }

//    public static ArrayList<Integer> getEdgeValidity(ArrayList<WordVertex> ed)
//    {
//        return new CustomArrayList<>(new Integer[]{
//                isSensibleEdge(ed) ? 1 : 0,
//                /*isSensibleEdge(ed, "tail") ? 1 : 0,
//                isSensibleEdge(ed, "head") ? 1 : 0,*/
//                isInComingSensibleEdge(ed) ? 1 : 0,
//                isPerfectAttaching(ed) ? 1 : 0
//        });
//    }

    private static Double WordAppearanceVariance = null;

    public static double getWordAppearanceVariance()
    {
        if (WordAppearanceVariance != null)
            return WordAppearanceVariance;
        var data = new ArrayList<Integer>();
        for (var word : WordAppearances.keySet())
            data.addAll(WordAppearances.get(word).values());
        WordAppearanceVariance = Utilities.variance(data);
        return WordAppearanceVariance;
    }

    private static Double WordAppearanceMean = null;

    public static double getWordAppearanceMean()
    {
        if (WordAppearanceMean != null)
            return WordAppearanceMean;
        var data = new ArrayList<Integer>();
        for (var word : WordAppearances.keySet())
            data.addAll(WordAppearances.get(word).values());
        WordAppearanceMean = Utilities.mean(data);
        return WordAppearanceMean;
    }

    public static ArrayList<String> getEdgeTypePair(ArrayList<WordVertex> ed)
    {
        var res = new ArrayList<String>();
        res.add(ed.get(0).Type);
        res.add(ed.get(1).Type);
        return res;
    }

    public static String getEdgeDirection(ArrayList<WordVertex> ed)
    {
        var v0 = ed.get(0);
        var v1 = ed.get(1);
        return v0.Location < v1.Location ? "next" : "before";
    }

    public static boolean checkInsideBalancedTypePair(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        var balancedTypePairs = getBalancedTypePairs();
        var dir = getEdgeDirection(ed);
        var inEds = Utilities.select(g.edgeList(),
                (x) -> x.get(1).equals(ed.get(1))
        );
        return Utilities.anyTrue(inEds, (ArrayList<WordVertex> x) ->
        {
            var pair = getEdgeTypePair(x);
            var xdir = getEdgeDirection(x);
            if (xdir.equals(dir))
                return false;
            if (balancedTypePairs.containsKey(pair) && balancedTypePairs.get(pair).containsKey(xdir))
            {
                var loc = balancedTypePairs.get(pair).get(xdir);
                var count = Utilities.count(inEds,
                        (y) -> getEdgeDirection(y).equals(dir)
                );
                return loc.equals("inside") && count == 0;
            } else return false;
        });
    }

    public static boolean checkOutsideBalancedTypePair(Graph<WordVertex> g, ArrayList<WordVertex> ed)
    {
        var balancedTypePairs = getBalancedTypePairs();
        var dir = getEdgeDirection(ed);
        var inEds = Utilities.select(g.edgeList(),
                (x) -> x.get(1).equals(ed.get(1))
        );
        return !Utilities.anyTrue(inEds, (ArrayList<WordVertex> x) ->
        {
            var pair = getEdgeTypePair(x);
            var xdir = getEdgeDirection(x);
            if (balancedTypePairs.containsKey(pair) && balancedTypePairs.get(pair).containsKey(xdir))
            {
                var loc = balancedTypePairs.get(pair).get(xdir);
                return loc.equals("outside") && !xdir.equals(dir);
            } else return false;
        });
    }

    private static int orderingf(Graph<WordVertex> g,
                                 ArrayList<WordVertex> ed0,
                                 ArrayList<WordVertex> ed1,
                                 HashSet<ArrayList<WordVertex>> currentEds,
                                 HashMap<String, Object> opts)
    {
        final var ignErrorsStr = "IgnoreErrors";
        var ignoreErrors = opts.containsKey(ignErrorsStr) ? (boolean) opts.get(ignErrorsStr) : false;
        NullFunction<Integer> errorCompareFunc = () ->
        {
            var auxg0 = new Graph<WordVertex>(g.vertexList(), Utilities.append(currentEds, ed0));
            var auxg1 = new Graph<WordVertex>(g.vertexList(), Utilities.append(currentEds, ed1));
            var errCompare = errorTreeCompare(auxg0, auxg1, ignoreErrors);
            if (errCompare != 0)
            {
                return errCompare < 0 ? -1 : 1;
            } else return 0;
        };
        var funcs = (ArrayList<NullFunction<Integer>>) Utilities.toArrayList(
                new NullFunction[]{errorCompareFunc}
        );
        for (var func : funcs)
        {
            var res = func.apply();
            if (res.intValue() != 0)
                return res;
        }
        return 0;
    }

    public static String mostCommonType1(String word, HashMap<ArrayList<String>, Double> PR, HashMap<String, String> assuming)
    {
        if (assuming.containsKey(word))
            return assuming.get(word);
        else
        {
            var values = WordAppearances.get(word).values();
            var maxValue = Utilities.max(values, (x, y) -> x - y);
            return Utilities.firstCase(WordAppearances.get(word).keySet(),
                    (x) -> WordAppearances.get(word).get(x).equals(maxValue)
            );
        }
    }

    public static String mostCommonType0(String word, HashMap<ArrayList<String>, Double> PR, HashMap<String, String> assuming)
    {
        if (assuming.containsKey(word))
            return assuming.get(word);
        else
        {
            String res = null;
            var currentValue = -1d;
            for (var pair : PR.keySet())
            {
                if (pair.get(0).equals(word))
                {
                    var value = PR.get(pair);
                    if (res == null || value > currentValue)
                    {
                        res = pair.get(1);
                        currentValue = PR.get(pair);
                    } else if (value == currentValue)
                    {
                        var appearance0 = WordAppearances.get(word).get(res);
                        var appearance1 = WordAppearances.get(word).get(pair.get(1));
                        if (appearance1 > appearance0)
                            res = pair.get(1);
                    }
                }
            }
            return res;
//            var values = new ArrayList<Integer>();
//            for (var type : wordAppearance.get(word).keySet())
//                values.add(wordAppearance.get(word).get(type));
//            var maxValue = Utilities.max(values, (x, y) -> x - y);
//            for (var type : wordAppearance.get(word).keySet())
//                if (wordAppearance.get(word).get(type).equals(maxValue))
//                    return type;
        }
//        throw new RuntimeException("error");
    }

    public static boolean isNaturalParserQ(Graph<WordVertex> g)
    {
        var vs = g.getVertices();
        var eds = g.getEdges();
        for (var v : vs)
        {
            if (!v.Type.equals("V"))
                continue;
            final UnaryFunction<WordVertex, Integer> getIndexFunc = (x) -> x.Location;
            var invs = g.inGoingVertices(v);
            var count0 = Utilities.count(invs,
                    (WordVertex w) ->
                    {
                        if (!w.Type.startsWith("N"))
                            return false;
                        var inCompos = g.vertexInComponent(w);
                        var indices = Utilities.map(getIndexFunc, inCompos);
                        var max = Utilities.max(indices, (z, t) -> z - t);
                        return max < v.Location;
                    });
            if (count0 >= 2)
            {
//                System.out.println(0);
                return false;
            }
            var Ns = Utilities.select(invs,
                    (WordVertex w) ->
                    {
                        if (!w.Type.startsWith("N"))
                            return false;
                        var inCompos = g.vertexInComponent(w);
                        var indices = Utilities.map(getIndexFunc, inCompos);
                        var min = Utilities.min(indices, (z, t) -> z - t);
                        return min > v.Location;
                    }
            );
            var count1 = Ns.size();
            if (count1 >= 3)
            {
//                System.out.println(1);
                return false;
            } else if (count1 == 2)
            {
                var words = Utilities.map((WordVertex x) -> x.Word, Ns);
                var firstWord = words.get(0);
                var check = Utilities.anyTrue(people, (String word) -> firstWord.startsWith(word));
                if (!check)
                {
//                    System.out.println(2);
                    return false;
                }
            }
            var Ns0 = Utilities.select(invs,
                    (WordVertex w) ->
                    {
                        if (!(w.Type.startsWith("N") || w.Type.equals("P")))
                            return false;
                        var inCompos = g.vertexInComponent(w);
                        var indices = Utilities.map(getIndexFunc, inCompos);
                        var max = Utilities.max(indices, (z, t) -> z - t);
                        return max < v.Location;
                    }
            );
            var Ns1 = Utilities.select(invs,
                    (WordVertex w) ->
                    {
                        if (!(w.Type.startsWith("N") || w.Type.equals("P")))
                            return false;
                        var inCompos = g.vertexInComponent(w);
                        var indices = Utilities.map(getIndexFunc, inCompos);
                        var max = Utilities.max(indices, (z, t) -> z - t);
                        return max > v.Location;
                    }
            );
            var Ns2 = Utilities.select(invs,
                    (WordVertex w) ->
                    {
                        if (!w.Type.equals("V"))
                            return false;
                        var inCompos = g.vertexInComponent(w);
                        var indices = Utilities.map(getIndexFunc, inCompos);
                        var max = Utilities.max(indices, (z, t) -> z - t);
                        return max > v.Location;
                    }
            );
            if (Ns0.size() > 0 && Ns1.size() > 0 && Ns2.size() > 0)
            {
                var indices1 = Utilities.map(getIndexFunc, Ns1);
                var min = Utilities.min(indices1, (z, t) -> z - t);
                var indices2 = Utilities.map(getIndexFunc, Ns2);
                var max = Utilities.max(indices2, (z, t) -> z - t);
                if (min < max)
                    return false;
            }
        }
        return true;
    }

    public static boolean isBinaryCurveSuitableIndicesQ(WordVertex u, WordVertex v, WordVertex w)
    {
        var ratio = 1d / 10;
        var word = u.Word;
        var uType = u.Type;
        UnaryFunction<String, String> simplifyN = (x) ->
        {
            if (x.startsWith("N"))
                return "N";
            else return x;
        };
        if (totalAppearance.get(word) >= waitingWordLeastSquares)
        {
            if (binaryCurveTypeConnection.containsKey(word))
            {
                var values = (ArrayList<Integer>) (Object) getLeafValues(binaryCurveTypeConnection.get(word));
                var max = Utilities.max(values, (x, y) -> x - y);
                var types = new CustomArrayList<String>(new String[]{
                        simplifyN.apply(u.Type), simplifyN.apply(v.Type), simplifyN.apply(w.Type)
                });
                ArrayList<Integer> indices = new CustomArrayList<Integer>(new Integer[]{
                        u.Location, v.Location, w.Location
                });
                indices = simplifyIndices(indices);
                if (keySequenceExistsQ(binaryCurveTypeConnection, word, types, indices))
                {
                    var lVs = (ArrayList<Integer>) (Object) getLeafValues(binaryCurveTypeConnection.get(word));
                    var value = binaryCurveTypeConnection.get(word).get(types).get(indices);
                    return value - Utilities.mean(lVs) > -0.5;
                } else return false;
            } else return false;
        } else return true;
    }

    public static boolean isTrivialCurveSuitableIndicesQ(WordVertex u, WordVertex v, WordVertex w)
    {
        var types = new CustomArrayList<String>(new String[]{
                u.Type, v.Type, w.Type
        });
        ArrayList<Integer> indices = new CustomArrayList<Integer>(new Integer[]{
                u.Location, v.Location, w.Location
        });
        indices = simplifyIndices(indices);
        return isTrivialCurveSuitableIndicesQ(new CustomArrayList<ArrayList<Object>>(
                new ArrayList[]{
                        types, indices
                }
        ));
    }

    public static boolean isTrivialCurveSuitableIndicesQ(ArrayList<ArrayList<Object>> info)
    {
        var types = (ArrayList<String>) (Object) info.get(0);
        var indices = (ArrayList<Integer>) (Object) info.get(1);
        if (!keySequenceExistsQ(curveTypeConnection, types, indices))
            return false;
        var auxValues = (ArrayList<Integer>) (Object) getLeafValues(curveTypeConnection.get(types));
        var auxValue = Utilities.sum(auxValues);
        if (auxValue < curveTypeConnectionLimit / 2)
            return true;
        var values = new ArrayList<Integer>();
        for (var key : curveTypeConnection.get(types).keySet())
            values.add(curveTypeConnection.get(types).get(key));
        var maxValue = Utilities.max(values, (x, y) -> x - y);
        var ratio = 1d / 5;
        var limit = maxValue * ratio;
        var value = (Integer) curveTypeConnection.get(types).get(indices);
        return value >= limit;
    }

    public static boolean isTypeConnectionSuitableIndicesQ(WordVertex a, WordVertex b, WordVertex c)
    {
        var Word = a.Word;
        if (!totalAppearance.containsKey(Word) || totalAppearance.get(Word) < appearanceLimit)
            return true;
        var types = new ArrayList<String>();
        types.add(a.Type);
        types.add(b.Type);
        types.add(c.Type);
        var indices = new ArrayList<Integer>();
        indices.add(a.Location);
        indices.add(b.Location);
        indices.add(c.Location);
        indices = simplifyIndices(indices);
        if (!keySequenceExistsQ(typeConnection, Word, types, indices))
            return false;
        var values = (ArrayList<Integer>) (Object) getLeafValues(typeConnection.get(Word).get(types));
        var maxValue = Utilities.max(values, (x, y) -> x - y);
        var value = ((Integer) getValue(typeConnection, Word, types, indices)).intValue();
//        System.out.println("type connection info: "+values+","+maxValue+","+value);
        return value >= maxValue.doubleValue() / 10;
    }


    public static void getTypeConnection()
    {
        typeConnection = new HashMap<>();
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            getTypeConnection(g, typeConnection);
        }
    }


    public static void getTypeConnection(Graph<WordVertex> g, HashMap out)
    {
        var res = new ArrayList<ArrayList<ArrayList<Object>>>();
        var vs = g.getVertices();
        for (var v : vs)
        {
            try
            {
                var v0 = v;
                var v1 = Utilities.getFirstElement(g.outGoingVertices(v0));
                var v2 = Utilities.getFirstElement(g.outGoingVertices(v1));
                var loc0 = v0.Location;
                var loc1 = v1.Location;
                var loc2 = v2.Location;
                var ar0 = new ArrayList<String>();
                ar0.add(v0.Type);
                ar0.add(v1.Type);
                ar0.add(v2.Type);
                var ar1 = new ArrayList<Integer>();
                ar1.add(loc0);
                ar1.add(loc1);
                ar1.add(loc2);
                ar1 = simplifyIndices(ar1);
                var word = v.Word;
                var value = 0;
                if (keySequenceExistsQ(out, word, ar0, ar1))
                    value = ((Integer) getValue(out, new Object[]{word, ar0, ar1})).intValue();
                insertValue(out, new Object[]{word, ar0, ar1}, value + 1);
            } catch (Exception e)
            {
            }
        }
    }

    public static ArrayList<Integer> simplifyIndices(ArrayList<Integer> ints)
    {
        var copied = new ArrayList<Integer>();
        for (var ele : ints)
            copied.add(ele);
        Utilities.quickSort(copied, (x, y) -> (x - y));
        var sim = new ArrayList<Integer>();
        for (var i = 0; i <= copied.size() - 1; i++)
            sim.add(i);
        var hm = new HashMap<Integer, Integer>();
        Utilities.mapThread((x, y) ->
        {
            hm.put(x, y);
        }, copied, sim);
        var res = new ArrayList<Integer>();
        for (var ele : ints)
            res.add(hm.get(ele));
        return res;
    }

    private static boolean isSorted(ArrayList<Integer> ints)
    {
        var size = ints.size();
        for (var i = 0; i <= size - 2; i++)
            if (ints.get(i) > ints.get(i + 1))
                return false;
        return true;
    }

    public static boolean pseudoIsValidGraph(Graph<WordVertex> g)
    {
        var vs = g.getVertices();
        for (var v : vs)
        {

            var vGroups = new ArrayList<ArrayList<Integer>>();
            {
                var locs = new ArrayList<Integer>();
                locs.add(v.Location);
                vGroups.add(locs);
            }
            var inVs = g.inGoingVertices(v);
            for (var w : inVs)
            {
                var compos = g.vertexInComponent(w);
                var locs = new ArrayList<Integer>();
                for (var s : compos)
                    locs.add(s.Location);
                Utilities.quickSort(locs,
                        (x, y) ->
                        {
                            return x - y;
                        }
                );
                vGroups.add(locs);
            }
            Utilities.quickSort(vGroups,
                    (group0, group1) ->
                    {
                        var x = group0.get(0);
                        var y = group1.get(0);
                        return x - y;
                    }
            );
            for (var i = 0; i <= vGroups.size() - 2; i++)
            {
                var iGroup = vGroups.get(i);
                var nextIGroup = vGroups.get(i + 1);
                var max = Utilities.max(iGroup, (x, y) -> x - y);
                var min = Utilities.min(nextIGroup, (x, y) -> x - y);
                if (!(max < min))
                    return false;
            }
        }
        return true;
    }

    public static boolean isValidGraph(Graph<WordVertex> g)
    {
        var vs = g.getVertices();
        for (var v : vs)
        {
            var vInCompos = g.vertexInComponent(v);
            var vInComposIndices = Utilities.map(
                    (WordVertex x) -> x.Location, vInCompos
            );
            Utilities.quickSort(vInComposIndices, (x, y) -> x - y);
            if (!isConsecutiveIntegers(vInComposIndices))
                return false;

            var vGroups = new ArrayList<ArrayList<Integer>>();
            {
                var locs = new ArrayList<Integer>();
                locs.add(v.Location);
                vGroups.add(locs);
            }
            var inVs = g.inGoingVertices(v);
            for (var w : inVs)
            {
                var compos = g.vertexInComponent(w);
                var locs = new ArrayList<Integer>();
                for (var s : compos)
                    locs.add(s.Location);
                Utilities.quickSort(locs,
                        (x, y) ->
                        {
                            return x - y;
                        }
                );
                vGroups.add(locs);
            }
            Utilities.quickSort(vGroups,
                    (group0, group1) ->
                    {
                        var x = group0.get(0);
                        var y = group1.get(0);
                        return x - y;
                    }
            );
            var lastEles = new ArrayList<Integer>();
            for (var i = 0; i <= vGroups.size() - 1; i++)
            {
                var iGroup = vGroups.get(i);
                lastEles.add(iGroup.get(iGroup.size() - 1));
            }
            if (!isSorted(lastEles))
                return false;
        }
        return true;
    }

    private static boolean isConsecutiveIntegers(ArrayList<Integer> ints)
    {
        var size = ints.size();
        for (var i = 0; i <= size - 2; i++)
        {
            var iEle = ints.get(i);
            var nextIEle = ints.get(i + 1);
            if ((nextIEle - iEle) != 1)
                return false;
        }
        return true;
    }

    public static boolean isEssentialLeafQ(Graph<WordVertex> g, WordVertex v)
    {
        var vs = g.vertexInComponent(v);
        vs.remove(v);
        return Utilities.allTrue(vs,
                (w) ->
                {
                    return w.Type.equals("R");
                }
        );
    }

    public static HashMap<WordVertex, Double> assignLevelFrequency(Graph g)
    {
        var wg = (Graph<WordVertex>) g.clone();
        var res = new HashMap<WordVertex, Double>();
        var runningLevel = 0;
        while (wg.vertexCount() > 0)
        {
            while (true)
            {
                var leaves = Utilities.select(wg.getVertices(),
                        (v) ->
                        {
                            return wg.vertexInDegree(v) == 0 && v.Type.equals("R");
                        }
                );
                if (leaves.size() == 0)
                    break;
                else
                {
                    for (var v : leaves)
                        wg.deleteVertex(v);
                }
            }
            if (wg.vertexCount() == 0)
                break;
            var leaves = Utilities.select(wg.getVertices(),
                    (v) ->
                    {
                        return wg.vertexInDegree(v) == 0;
                    }
            );
            for (var v : leaves)
            {
                var word = v.Word;
                var type = v.Type;
                var value = 0d;
                var lAHm = (HashMap<Object, Object>) (Object) levelAppearance;
                if (keySequenceExistsQ(lAHm, word, type, runningLevel))
                {
                    var intValue = ((Integer) getValue(lAHm, word, type, runningLevel)).intValue();
                    value = (double) intValue;
                }
                if (value == 0d)
                    res.put(v, 0d);
                else res.put(v, value / totalAppearance.get(word));
            }
            for (var v : leaves)
                wg.deleteVertex(v);
            runningLevel++;
        }
        return res;
    }

    public static Graph<WordVertex> randomRootedSpanningTree(Graph<WordVertex> g, WordVertex root)
    {
        return preRandomRootedSpanningTree(g, root,
                (v0, v1) ->
                {
                    return v0.Word.equals(v1.Word);
                }
        );
    }

    public static <T> Graph<T> preRandomRootedSpanningTree(Graph<T> g, T root, BinaryFunction<T, T, Boolean> sameVertexQ)
    {
        var res = new Graph<T>();
        res.addVertex(root);
        var rand = new Random();
        while (true)
        {
            var selectedEds = Utilities.select(g.getEdges(),
                    (ed) ->
                    {
                        var v0 = ed.get(0);
                        var v1 = ed.get(1);
                        var vs = res.getVertices();
                        var inQ = false;
                        for (var v : vs)
                        {
                            if (sameVertexQ.apply(v, v0))
                            {
                                inQ = true;
                                break;
                            }
                        }
                        return !inQ && res.containsVertex(v1);
                    }
            );
            var size = selectedEds.size();
            if (size == 0)
                break;
            var chosenPos = rand.nextInt(size);
            var chosenEd = selectedEds.get(chosenPos);
            var v0 = chosenEd.get(0);
            var v1 = chosenEd.get(1);
            res.addVertex(chosenEd.get(0));
            res.addEdge(chosenEd);
            try
            {
                var edgeWeight = g.getEdgeWeight(v0, v1);
//                if (edgeWeight != null)
                res.setEdgeWeight(v0, v1, edgeWeight);
            } catch (Exception e)
            {
            }
        }
        return res;
    }

    public static Graph oldMakeDependenceGraph(ArrayList<String> sentence, HashMap<String, String> assuming)
    {
        var wordTypes = new HashMap<Integer, HashSet<String>>();
        for (var i = 0; i <= sentence.size() - 1; i++)
        {
            wordTypes.put(i, new HashSet<>());
            var iWord = sentence.get(i);
            if (WordAppearances.containsKey(iWord))
                wordTypes.get(i).addAll(WordAppearances.get(iWord).keySet());
            if (assuming.containsKey(iWord))
                wordTypes.get(i).add(assuming.get(iWord));
        }
        var eds = new HashSet<ArrayList<WordVertex>>();
        var edgeWeights = new HashMap<ArrayList<WordVertex>, Integer>();
        var limit = getApperanceMean() + getApperanceVariance();
        TernaryAction<HashMap<String, HashMap<String, HashMap<String, Integer>>>, String, HashMap<
                String, Integer>> action = (typeDep, type, hm) ->
        {
            for (var opType : typeDep.get(type).keySet())
            {
                if (!opType.startsWith("N"))
                    continue;
                for (var dir : typeDep.get(type).get(opType).keySet())
                {
                    var freq = typeDep.get(type).get(opType).get(dir);
                    if (!hm.containsKey(dir))
                        hm.put(dir, 0);
                    var value = hm.get(dir);
                    hm.put(dir, value + freq);
                }
            }
        };
        for (var i = 0; i <= sentence.size() - 1; i++)
        {
            var iWord = sentence.get(i);
            var check0 = totalAppearance.containsKey(iWord) && totalAppearance.get(iWord) < limit;
            var check1 = !totalAppearance.containsKey(iWord) && assuming.containsKey(iWord);
            for (var j = 0; j <= sentence.size() - 1; j++)
            {
                if (i == j)
                    continue;
                var jWord = sentence.get(j);
                var direction = i < j ? "next" : "before";
                for (var iType : wordTypes.get(i))
                {
                    var hm = new HashMap<String, Integer>();
                    if (check0 || check1)
                        action.apply(typeDependency, iType, hm);
                    var iVertex = new WordVertex(i, sentence.get(i), iType);
                    for (var jType : wordTypes.get(j))
                    {
                        var jVertex = new WordVertex(j, sentence.get(j), jType);
                        var ed = new ArrayList<WordVertex>();
                        ed.add(iVertex);
                        ed.add(jVertex);
                        try
                        {
                            if (check0 || check1)
                            {
                                Integer weight;
                                if (!jType.startsWith("N"))
                                    weight = typeDependency.get(iType).get(jType).get(direction);
                                else weight = hm.get(direction);
                                if (weight != null)
                                {
                                    edgeWeights.put(ed, weight);
                                    eds.add(ed);
                                }
                            } else
                            {
                                var mimicTypeDependence = outWordDependence.get(iWord);
                                var hm2 = new HashMap<String, Integer>();
                                action.apply(mimicTypeDependence, iType, hm2);
                                Integer weight;
                                if (!jType.startsWith("N"))
                                    weight = outWordDependence.get(iWord).get(iType).get(jType).get(direction);
                                else weight = hm2.get(direction);
                                if (weight != null)
                                    if (weight >= 5)
                                    {
                                        eds.add(ed);
                                        edgeWeights.put(ed, weight);
                                    }
                            }
                        } catch (Exception e)
                        {
                            continue;
                        }
                    }
                }
            }
        }
        var res = new Graph();
        for (var ed : eds)
        {
            try
            {
                var v0 = ed.get(0);
                var v1 = ed.get(1);
                res.addEdge(v0, v1);
                var weight = edgeWeights.get(ed);
                res.setEdgeWeight(v0, v1, weight);
            } catch (Exception e)
            {
            }
        }
        return res;
    }

    public static double getApperanceVariance()
    {
        var mean = getApperanceMean();
        double squareSum = 0;
        for (var word : totalAppearance.keySet())
        {
            var value = totalAppearance.get(word);
            squareSum += ((value - mean) * (value - mean));
        }
        return Math.sqrt(squareSum / totalAppearance.size());
    }

    /**
     * hàm này chỉ phân biệt từ chứ không phân biệt kiểu của từ
     *
     * @return
     */
    public static double getApperanceMean()
    {
        var res = 0;
        for (var word : totalAppearance.keySet())
            res += totalAppearance.get(word);
        return (double) res / totalAppearance.size();
    }

    public static void getLevelAppearance()
    {
        levelAppearance = new HashMap<>();
        var lAObj = (HashMap<Object, Object>) (Object) levelAppearance;
        for (var parser : Parsers)
        {
            var g = getDependenceGraph(parser);
            var levelAp = getLevelAppearance(g);
            for (var word : levelAp.keySet())
                for (var type : levelAp.get(word).keySet())
                    for (var level : levelAp.get(word).get(type).keySet())
                    {
                        if (!keySequenceExistsQ(lAObj, word, type, level))
                            insertValue(lAObj, new Object[]{word, type, level}, 0);
                        var value = (Integer) getValue(lAObj, word, type, level);
                        insertValue(lAObj, new Object[]{word, type, level}, value + 1);
                    }
        }
    }

    public static HashMap<String, HashMap<String, HashMap<Integer, Integer>>> getLevelAppearance(Graph<WordVertex> g)
    {
        var wg = (Graph<WordVertex>) g.clone();
        var res = new HashMap<String, HashMap<String, HashMap<Integer, Integer>>>();
        var runningLevel = 0;
        while (wg.vertexCount() > 0)
        {
            while (true)
            {
                var leaves = Utilities.select(wg.getVertices(),
                        (v) ->
                        {
                            if (wg.vertexInDegree(v) != 0)
                                return false;
                            if (v.Type.equals("R"))
                                return true;
                            var outVs = wg.outGoingVertices(v);
                            if (outVs.size() == 0)
                                return false;
                            else
                            {
                                var outV = Utilities.getFirstElement(outVs);
                                return v.Type.equals("A") && outV.Type.equals("V");
                            }
                        }
                );
                if (leaves.size() == 0)
                    break;
                for (var leaf : leaves)
                    wg.deleteVertex(leaf);
            }
            if (wg.vertexCount() == 0)
                break;
            var leaves = Utilities.select(wg.getVertices(),
                    (v) ->
                    {
                        return wg.vertexInDegree(v) == 0;
                    }
            );
            var resObj = (HashMap<Object, Object>) (Object) res;
            for (var leaf : leaves)
            {
                var originLeaf = (WordVertex) leaf;
                var word = originLeaf.Word;
                var type = originLeaf.Type;
                if (!keySequenceExistsQ(resObj, word, type, runningLevel))
                    insertValue(resObj, new Object[]{word, type, runningLevel}, 0);
                var value = (Integer) getValue(resObj, word, type, runningLevel);
                insertValue(resObj, new Object[]{word, type, runningLevel}, value + 1);
            }
            for (var leaf : leaves)
                wg.deleteVertex(leaf);
            runningLevel++;
        }
        return res;
    }

    public static void getTypeDependency()
    {
        typeDependency = new HashMap<>();
        for (var parser : Parsers)
        {
            var gr = getDependenceGraph(parser);
            for (var ed : gr.getEdges())
            {
                var v0 = (WordVertex) ed.get(0);
                var v1 = (WordVertex) ed.get(1);
                var type0 = v0.Type;
                var type1 = v1.Type;
                var direction = v0.Location < v1.Location ? "next" : "before";
                var tDobj = (HashMap<Object, Object>) (Object) typeDependency;
                if (!keySequenceExistsQ(tDobj, type0, type1, direction))
                    insertValue(tDobj, new Object[]{type0, type1, direction}, 0);
                var value = (Integer) getValue(tDobj, type0, type1, direction);
                insertValue(tDobj, new Object[]{type0, type1, direction}, value + 1);
            }
        }
    }

    private static <S, T, U> Object getValue(HashMap<S, T> hm, U... keys)
    {
        Object res = hm;
        for (var key : keys)
        {
            if (!(res instanceof HashMap))
                return null;
            var origin = (HashMap<Object, Object>) res;
            if (!origin.containsKey(key))
                return null;
            res = origin.get(key);
        }
        return res;
    }

    public static <S, T, U> void increaseValue(HashMap<S, T> hm, U[] keys, int value)
    {
        if (!keySequenceExistsQ(hm, keys))
            insertValue(hm, keys, 0);
        var currentValue = (Integer) getValue(hm, keys);
        insertValue(hm, keys, currentValue + value);
    }

    private static <S, T, U, V> void insertValue(HashMap<S, T> hm, U[] keys, V value)
    {
        Object running = hm;
        for (var i = 0; i <= keys.length - 2; i++)
        {
            var key = keys[i];
            if (!(hm instanceof HashMap))
                return;
            var origin = (HashMap<Object, Object>) running;
            if (!origin.containsKey(key))
                origin.put(key, new HashMap<>());
            running = origin.get(key);
        }
        if (!(running instanceof HashMap))
            return;
        var origin = (HashMap<Object, Object>) running;
        var lastKey = keys[keys.length - 1];
        origin.put(lastKey, value);
    }


    private static <S, T, U> boolean keySequenceExistsQ(HashMap<S, T> hm, U... keys)
    {
        Object running = hm;
        for (var i = 0; i <= keys.length - 1; i++)
        {
            var key = keys[i];
            if (!(running instanceof HashMap))
                return false;
            var origin = (HashMap) running;
            if (!origin.containsKey(key))
                return false;
            running = origin.get(key);
        }
        return true;
    }


    public static HashMap<String, HashMap<String, Integer>> getWordAppearances()
    {
        if (WordAppearances != null)
            return WordAppearances;
        WordAppearances = new HashMap<>();
        for (var parser : Parsers)
        {
            var tree = getDependenceGraph(parser);
            for (var v : tree.vertexList())
            {
                Utilities.insertValue(WordAppearances,
                        new Object[]{v.Word, v.Type}, 0, (x) -> x + 1
                );
            }
        }
        return WordAppearances;
    }

    public static void getTotalAppearance()
    {
        totalAppearance = new HashMap<>();
        for (var parser : Parsers)
        {
            var gr = getDependenceGraph(parser);
            for (var v : gr.getVertices())
            {
                var word = ((WordVertex) v).Word;
                if (!totalAppearance.containsKey(word))
                    totalAppearance.put(word, 0);
                var value = totalAppearance.get(word);
                totalAppearance.put(word, value + 1);
            }
        }
    }

    public static String normalizeUnderscoredWord(String s)
    {
        var splits = s.split("_");
        var selecteds = new ArrayList<String>();
        for (var ele : splits)
            if (ele.length() > 0)
                selecteds.add(ele);
        var res = "";
        for (var i = 0; i <= selecteds.size() - 1; i++)
        {
            var iWord = selecteds.get(i)/*.toLowerCase()*/;
            if (i == 0)
                res += iWord;
            else res += (" " + iWord);
        }
        return res;
    }

    public static void getWordDependence()
    {
        outWordDependence = new HashMap<>();
        for (var parser : Parsers)
        {
            var gr = getDependenceGraph(parser);
            var eds = (HashSet<ArrayList<WordVertex>>) ((Object) gr.getEdges());
            for (var ed : eds)
            {
                var v0 = ed.get(0);
                var word = v0.Word;
                var type0 = v0.Type;
                var v1 = ed.get(1);
                var type1 = v1.Type;
                var direction = v0.Location < v1.Location ? "next" : "before";
                if (!outWordDependence.containsKey(word))
                    outWordDependence.put(word, new HashMap<>());
                if (!outWordDependence.get(word).containsKey(type0))
                    outWordDependence.get(word).put(type0, new HashMap<>());
                if (!outWordDependence.get(word).get(type0).containsKey(type1))
                    outWordDependence.get(word).get(type0).put(type1, new HashMap<>());
                if (!outWordDependence.get(word).get(type0).get(type1).containsKey(direction))
                    outWordDependence.get(word).get(type0).get(type1).put(direction, 0);
                var value = outWordDependence.get(word).get(type0).get(type1).get(direction);
                outWordDependence.get(word).get(type0).get(type1).put(direction, value + 1);
            }
        }
    }

    private static CustomHashSet<Character> trivialCharacters = new CustomHashSet<>(
            new Character[]{' ', '_', '.', '\"', '-', ':', '!', '?', '%'}
    );

    private static boolean isValidWord(String word)
    {
        for (var i = 0; i <= word.length() - 1; i++)
        {
            var ic = word.charAt(i);
            if (!trivialCharacters.contains(ic))
                return true;
        }
        return false;
    }

    public static Graph<WordVertex> getDependenceGraph(ArrayList<ArrayList<String>> parser)
    {
        var res = new Graph<WordVertex>();
        for (var row : parser)
        {
            try
            {
                var loc = Integer.parseInt(row.get(0));
                var word = row.get(1)/*.toLowerCase()*/;
                if (!isValidWord(word))
                    continue;
                var type = row.get(2);
                if (!type.equals("Np"))
                    word = word.toLowerCase();
                word = normalizeUnderscoredWord(word);
                var connectedTo = Integer.parseInt(row.get(3));
                var connectedRow = parser.get(connectedTo - 1);
                var cloc = Integer.parseInt(connectedRow.get(0));
                var cword = connectedRow.get(1)/*.toLowerCase()*/;
                if (!isValidWord(cword))
                    continue;
                var ctype = connectedRow.get(2);
                if (!ctype.equals("Np"))
                    cword = cword.toLowerCase();
                cword = normalizeUnderscoredWord(cword);
                var vertex0 = new WordVertex(loc, word, type);
                var vertex1 = new WordVertex(cloc, cword, ctype);
                res.addVertex(vertex0);
                res.addVertex(vertex1);
                res.addEdge(vertex0, vertex1);
            } catch (Exception e)
            {
            }
        }
        return res;
    }

    public static boolean isQuestionQ(ArrayList<ArrayList<String>> sentence)
    {
        for (var row : sentence)
        {
            try
            {
                var loc = Integer.parseInt(row.get(0));
                var word = row.get(1);
                if (word.equals("?"))
                    return true;
            } catch (Exception e)
            {
            }
        }
        return false;
    }

    private static void initializeForbiddenTypeConnections()
    {
        forbiddenTypeConnections = new HashSet<ArrayList<String>>();
        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"E", "N", "N"}));
        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"V", "N", "N"}));
        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"A", "E"}));
        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"E", "A"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "P"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "Np"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "Nu"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "Ny"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "N"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "NP"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "Nb"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"R", "Nc"}));
        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{"M", "E"}));
        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{null, "R"}));
//        forbiddenTypeConnections.add(new CustomArrayList<String>(new String[]{null, "A", "V"}));
    }

    public static void initialize()
    {
        var obj = new VietnameseAnalyzer();
        VietnameseAnalyzer.Parsers = obj.getDataFromFile();
        getWordAppearances();
        VietnameseAnalyzer.getErrorAppearanceStatics();
        VietnameseAnalyzer.isInitialized = true;
    }

    public ArrayList<ArrayList<ArrayList<String>>> getDataFromFile() throws RuntimeException
    {
        var res = new ArrayList<ArrayList<ArrayList<String>>>();
        String path = null;
        try
        {
            var iS = this.getClass().getClassLoader().getResourceAsStream("vtb.txt");
            InputStreamReader isr = new InputStreamReader(iS, StandardCharsets.UTF_8);
            BufferedReader reader = new BufferedReader(isr);

            ArrayList<ArrayList<String>> runningParser = new ArrayList<>();
            ArrayList<String> row = null;
            String s;
            var balance = 0;

            while ((s = reader.readLine()) != null)
            {
                if (s.equals("{"))
                {
                    balance++;
                    if (balance == 1)
                        runningParser = new ArrayList<>();
                    if (balance == 2)
                        row = new ArrayList<>();
                } else if (s.equals("}"))
                {
                    balance--;
                    if (balance == 1)
                        runningParser.add(row);
                    if (balance == 0)
                        res.add(runningParser);
                } else
                {
                    row.add(s);
                }
            }
        } catch (Exception e)
        {
            throw new RuntimeException(path);
        }
        return res;
    }
}
