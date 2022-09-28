package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.TypeName;

import org.junit.Before;
import org.junit.Test;

import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;

public class DafnyTest {
    Dafny underTest;

    @Before
    public void setup() {
        String rawModel = """
                namespace smithy.example
                service Example {}
                resource MyResource {}
                list MyList { member: String }
                map MyMap { key: String, value: String }
                structure MyStructure {}
                """;
        underTest = setupLocalModel(rawModel, "Dafny.Smithy.Example", "smithy.example");
    }

    @Test
    public void packageName() {
        final String expected = "Dafny.Smithy.Example";
        final String actual = underTest.packageName();
        assertEquals(expected, actual);
    }

    @Test
    public void typeForShapeBlob() {
        final String expected = "dafny.DafnySequence<? extends java.lang.Byte>";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.api", "Blob"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeBoolean() {
        final String expected = "java.lang.Boolean";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.api", "Boolean"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeString() {
        final String expected = "dafny.DafnySequence<? extends java.lang.Character>";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.api", "String"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeInteger() {
        final String expected = "java.lang.Integer";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.api", "Integer"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeTimestamp() {
        final String expected = "dafny.DafnySequence<? extends java.lang.Character>";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.api", "Timestamp"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeListOfStrings() {
        final String expected = "dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Character>>";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.example", "MyList"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeMapKeyStringValueString() {
        final String expected = "dafny.DafnyMap<" +
                "? extends dafny.DafnySequence<? extends java.lang.Character>, " +
                "? extends dafny.DafnySequence<? extends java.lang.Character>" +
                ">";
        final TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.example", "MyMap"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeMember() {
    }

    @Test
    public void typeForShapeStructure() {
        final String expected = "Dafny.Smithy.Example.Types.MyStructure";
        TypeName actual = underTest.typeForShape(ShapeId.fromParts("smithy.example", "MyStructure"));
        final String actualString = actual.toString();
        assertEquals(expected, actualString);
    }

    @Test
    public void typeForShapeService() {
        assertThrows(UnsupportedOperationException.class,
                () -> underTest.typeForShape(ShapeId.fromParts("smithy.example", "Example")));
    }

    @Test
    public void typeForShapeResource() {
        assertThrows(UnsupportedOperationException.class,
                () -> underTest.typeForShape(ShapeId.fromParts("smithy.example", "MyResource")));
    }

    static Dafny setupLocalModel(
            String rawModel,
            String packageName,
            String nameSpace
    ) {
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        ServiceShape serviceShape = ModelUtils.serviceFromNamespace(localModel, nameSpace);
        return new Dafny(packageName, localModel, serviceShape);
    }
}
