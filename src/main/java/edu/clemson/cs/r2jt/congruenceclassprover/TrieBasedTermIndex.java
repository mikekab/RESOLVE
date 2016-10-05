package edu.clemson.cs.r2jt.congruenceclassprover;
import java.util.*;

/**
 * Created by Mike on 10/4/2016.
 */

public class TrieBasedTermIndex {

    public Node m_root;
    public TrieBasedTermIndex(){
        m_root = new Node();
    }
    private class Node{
        int label = 0;
        public TreeMap<Integer,Node> children;
        public Node(){
            children = new TreeMap<>();
        }
    }

    public void insert(int[] term, int value){
        int sz = term.length;
        Node cur = m_root;
        int idx = 0;
        while(idx<sz){
            if(cur.children.containsKey(term[idx])){
                cur = cur.children.get(term[idx]);
                ++idx;
            }
            else break;
        }
        while(idx < sz){
            cur.children.put(term[idx],new Node());
            cur = cur.children.get(term[idx]);
            idx++;
        }
        cur.label = value;
    }
    public Set<Integer> find(Node n, int[]key, int pos){

        Set<Integer> generalizations = new HashSet<>();
        if(pos < key.length) {
            if (n.children.containsKey(key[pos])) {
                if (n.children.get(key[pos]).children.isEmpty()) {
                    generalizations.add(n.children.get(key[pos]).label);
                } else generalizations = find(n.children.get(key[pos]), key, pos + 1);
            }
            if (n.children.containsKey(0)) {
                if (n.children.get(0).children.isEmpty()) {
                    generalizations.add(n.children.get(0).label);
                } else {
                    generalizations.addAll(find(n.children.get(0), key, pos + 1));
                }
            }
        }
        return generalizations;
    }

    public String test(){
        String rS = "";
        insert(new int[]{1,0,0},1);//f(x,y)
        insert(new int[]{0,0,0},2);//u(x,y)
        insert(new int[]{1,2,0},3);//f(a,x)
        insert(new int[]{1,0,2},4);//f(x,a)
        insert(new int[]{0,2,0},5);//u(a,x)

        Set<Integer> gens = find(m_root,new int[]{1,0,0},0); // find f(x,y). should be 1,2
        rS += gens + "\n";
        gens = find(m_root,new int[]{1,2,2},0);// find f(a,a). should be 1,2,3,4,5
        rS += gens + "\n";
        gens = find(m_root,new int[]{1,2,0},0);//find f(a,x). should be 1,2,3,5
        rS += gens + "\n";
        int i = 0;
        return rS;
    }

}
