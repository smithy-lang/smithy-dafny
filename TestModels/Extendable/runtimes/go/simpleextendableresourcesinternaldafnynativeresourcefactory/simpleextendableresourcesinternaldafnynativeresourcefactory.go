// Package simpleextendableresourcesinternaldafnynativeresourcefactory
// Dafny module simpleextendableresourcesinternaldafnynativeresourcefactory compiled into Go

package simpleextendableresourcesinternaldafnynativeresourcefactory

import (
	"os"

	"github.com/Smithy-dafny/TestModels/Extendable/ExtendableResource"
	"github.com/Smithy-dafny/TestModels/Extendable/SimpleExtendableResourcesOperations"
	"github.com/Smithy-dafny/TestModels/Extendable/simpleextendableresources"
	"github.com/Smithy-dafny/TestModels/Extendable/simpleextendableresourcesinternaldafnytypes"
	"github.com/dafny-lang/DafnyRuntimeGo/dafny"
	"github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	"github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	"github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	"github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
)

var _ = os.Args
var _ dafny.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ ExtendableResource.Dummy__
var _ SimpleExtendableResourcesOperations.Dummy__

type Dummy__ struct{}

func DafnyFactory() simpleextendableresourcesinternaldafnytypes.IExtendableResource {
	extendableResource := ExtendableResource.New_ExtendableResource_()
	extendableResource.OfName(dafny.SeqOfString("dafny-default"))
	return &simpleextendableresources.NativeWrapper{Impl: simpleextendableresources.ExtendableResource_FromDafny(extendableResource)}
}
