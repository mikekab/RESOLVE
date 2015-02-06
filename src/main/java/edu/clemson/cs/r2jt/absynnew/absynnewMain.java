package edu.clemson.cs.r2jt.absynnew;

import edu.clemson.cs.r2jt.parsing.ResolveParser;
import org.antlr.v4.runtime.ANTLRFileStream;

import java.io.IOException;

/**
 * <p>A test main intended exclusively for the new absyn package.</p>
 */
public class absynnewMain {

    public static final ResolveParserFactory PARSER_FACTORY =
            new ResolveParserFactory();

    public static void main(String[] args) {
        try {
            ResolveParser parser =
                    PARSER_FACTORY.createParser(new ANTLRFileStream(args[0]));
            ModuleAST result = TreeUtil.createASTNodeFrom(parser.module());

        }
        catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }

    }
}
