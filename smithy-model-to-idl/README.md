# Smithy model to IDL

This is a simple wrapper around [Smithy's `SmithyIdlModelSerializer`](https://github.com/awslabs/smithy/blob/main/smithy-model/src/main/java/software/amazon/smithy/model/shapes/SmithyIdlModelSerializer.java),
which allows to serialize a Smithy model (for example, one loaded from a JSON file) into Smithy IDL
in order to improve its legibility.

## Usage

Prerequisites:

- Java 16 or above
- A model you want to serialize at `$MODEL_PATH`, e.g. the [KMS JSON model](https://github.com/aws/aws-models/blob/master/kms/smithy/model.json)
- A clone of the [Smithy repository](https://github.com/awslabs/smithy) at `$SMITHY_REPO_PATH`
- An output directory for the serialized models at `$DEST_PATH`

```bash
$ # start in project root
$ pwd
~/Polymorph-smithy-dotnet/smithy-model-to-idl

$ # build
$ ./gradlew build
BUILD SUCCESSFUL in 507ms

$ # serialize
$ ./gradlew run --args="$DEST_PATH $SMITHY_REPO_PATH $MODEL_PATH"
...
INFO: Wrote /.../com.amazonaws.kms.smithy
...
```

If you want to serialize multiple aws models at once, simply append those paths as arguments.
For example:
```
$ # serialize
$ ./gradlew run --args="$DEST_PATH $SMITHY_REPO_PATH /path/to/aws-models/kms/smithy/model.json /path/to/aws-models/dynamodb/smithy/model.json"
...
INFO: Wrote /.../com.amazonaws.kms.smithy
...
INFO: Wrote /Users/lavaleri/smithy-model-output/com.amazonaws.dynamodb.smithy
...
```

You'll find several files in `$DEST_PATH`,
including one for the model you specified (e.g. `$DEST_PATH/com.amazonaws.kms.smithy`)
and others for various namespaces found in the Smithy models.
