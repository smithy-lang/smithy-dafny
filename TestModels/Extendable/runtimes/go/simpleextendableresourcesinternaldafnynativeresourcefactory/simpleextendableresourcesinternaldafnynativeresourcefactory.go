// Package simpleextendableresourcesinternaldafnynativeresourcefactory
// Dafny module simpleextendableresourcesinternaldafnynativeresourcefactory compiled into Go

package simpleextendableresourcesinternaldafnynativeresourcefactory

import (
	os "os"

	ExtendableResource "ExtendableResource"
	"simpleextendableresources"

	SimpleExtendableResourcesOperations "SimpleExtendableResourcesOperations"
	StandardLibrary "StandardLibrary"
	StandardLibraryInterop "StandardLibraryInterop"
	StandardLibrary_UInt "StandardLibrary_UInt"
	_System "System_"
	TestHelpers "TestHelpers"
	Wrappers "Wrappers"
	_dafny "dafny"
	simpleextendableresourcesinternaldafnytypes "simpleextendableresourcesinternaldafnytypes"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ ExtendableResource.Dummy__
var _ SimpleExtendableResourcesOperations.Dummy__
var _ TestHelpers.Dummy__

type Dummy__ struct{}

func DafnyFactory() simpleextendableresourcesinternaldafnytypes.IExtendableResource {
	extendableResource := ExtendableResource.New_ExtendableResource_()
	extendableResource.OfName(_dafny.SeqOfString("dafny-default"))
	return &simpleextendableresources.NativeWrapper{Impl: simpleextendableresources.ToNativeExtendableResource(extendableResource)}
}
