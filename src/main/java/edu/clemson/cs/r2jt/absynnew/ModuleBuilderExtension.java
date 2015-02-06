package edu.clemson.cs.r2jt.absynnew;

import edu.clemson.cs.r2jt.absynnew.decl.ModuleParameterAST;
import edu.clemson.cs.r2jt.absynnew.expr.ExprAST;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

/**
 * <p>I don't really know yet how much I like the smell of this abstract module
 * builder class. Though for now if it works I'll use it since it lets me avoid
 * re-writing three methods the exact same way four times over.</p>
 * 
 * @param <E> The module builder. (weird, I know.)
 * 
 * @see <href>http://en.wikipedia.org/wiki/Curiously_recurring_template_pattern</href>
 */
public abstract class ModuleBuilderExtension<E extends ModuleBuilderExtension<E>>
        extends
        AbstractNodeBuilder<ModuleAST> {

    public ModuleBlockAST block;
    public ExprAST requires = null;

    public final List<ModuleParameterAST> moduleParameters =
            new ArrayList<ModuleParameterAST>();

    public ImportBlockAST usesBlock = null;
    public final Token name;

    public ModuleBuilderExtension(Token start, Token stop, Token name) {
        super(start, stop);
        this.name = name;
    }

    public Token getName() {
        return name;
    }

    @SuppressWarnings("unchecked")
    public E parameters(List<ModuleParameterAST> e) {
        sanityCheckAdditions(e);
        moduleParameters.addAll(e);
        return (E) this;
    }

    @SuppressWarnings("unchecked")
    public E imports(ImportBlockAST e) {
        usesBlock = e;
        return (E) this;
    }

    @SuppressWarnings("unchecked")
    public E requires(ExprAST e) {
        requires = e;
        return (E) this;
    }

    @SuppressWarnings("unchecked")
    public E usesBlock(ImportBlockAST e) {
        usesBlock = e;
        return (E) this;
    }

    @SuppressWarnings("unchecked")
    public E block(ModuleBlockAST e) {
        block = e == null ? ModuleBlockAST.EMPTY_BLOCK : e;
        return (E) this;
    }
}