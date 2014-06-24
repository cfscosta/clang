//===--- SemaCLI.cpp - Semantic Analysis for C++/CLI-----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic analysis for C++/CLI language constructs.
//
//===----------------------------------------------------------------------===//

#include "clang/Sema/Sema.h"
#include "clang/Sema/SemaCLI.h"
#include "clang/Sema/SemaInternal.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Scope.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/DeclCLI.h"
#include "clang/AST/TypeCLI.h"
#include "clang/AST/CXXInheritance.h"
#include "llvm/ADT/StringExtras.h"
#include "TypeLocBuilder.h"

#include <mono/metadata/assembly.h>
#include <mono/metadata/cil-coff.h>
#include <mono/metadata/class.h>
#include <mono/metadata/class-internals.h>
#include <mono/metadata/debug-helpers.h>
#include <mono/metadata/image.h>
#include <mono/metadata/loader.h>
#include <mono/metadata/metadata-internals.h>
#include <mono/metadata/mono-endian.h>
#include <mono/metadata/mono-config.h>
#include <mono/metadata/tabledefs.h>
#include <mono/metadata/appdomain.h>
#include <mono/utils/mono-digest.h>
#include <mono/metadata/tokentype.h>
#include <mono/metadata/attrdefs.h>
#include <mono/utils/bsearch.h>

#include <string>


#using <System.dll>
using namespace System;
using namespace System::IO;
using namespace System::Collections::Generic;
using namespace System::Runtime::InteropServices;

#using <Mono.Cecil.dll>
using namespace Mono::Cecil;

#include "CLIInterop.h"
#include <vcclr.h>

#pragma comment(lib, "F:\\mono\\msvc\\mono.lib")
namespace DllImport{

class MetaTable{
public:
  const MonoTableInfo *TheTable;
  unsigned int size;
  unsigned int tabsize;
  guint32 *cols;
  MetaTable(MonoImage* image, MonoMetaTableEnum table, unsigned int itabsize){
    TheTable = mono_image_get_table_info (image, table);
    size = mono_table_info_get_rows (TheTable);
    tabsize=itabsize;
    cols = (guint32*)malloc(sizeof(guint32)*tabsize);
  }
  guint32* getRow(int row){
    if (row >= size)
      return NULL;
    else
      mono_metadata_decode_row (TheTable, row, cols, tabsize);
    return cols;
  }
};

class TypeRef {
public:
  int index;
  int resolutionScope;
  std::string Name;
  std::string Namespace;
  MetaTable* TheTable;
  MonoImage *image;
  TypeRef(int iindex, MonoImage *img){
    image = img;
    index=iindex;
    Name ="";
    Namespace="";
    TheTable = new MetaTable(image, MONO_TABLE_TYPEDEF, MONO_TYPEDEF_SIZE);
    guint32 *cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    resolutionScope = cols [MONO_TYPEREF_SCOPE];
    Name = mono_metadata_string_heap (image, cols[MONO_TYPEREF_NAME]);
    Namespace = mono_metadata_string_heap (image, cols[MONO_TYPEREF_NAMESPACE]);
  }

  void get(int iindex){
    Name ="";
    Namespace="";
    guint32 *cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    resolutionScope = cols [MONO_TYPEREF_SCOPE];
    Name = mono_metadata_string_heap (image, cols[MONO_TYPEREF_NAME]);
    Namespace = mono_metadata_string_heap (image, cols[MONO_TYPEREF_NAMESPACE]);
  }
};

class Assembly{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int HashAlg;
  unsigned int MajorVersion;
  unsigned int MinorVersion;
  unsigned int BuildNumber;
  unsigned int RevNumber;
  unsigned int Flags;
  guint32 PublicKey;
  std::string Name;
  std::string Culture;

  Assembly(int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_ASSEMBLY	,MONO_ASSEMBLY_SIZE);
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;

    HashAlg = cols[MONO_ASSEMBLY_HASH_ALG];
    MajorVersion = cols[MONO_ASSEMBLY_MAJOR_VERSION];
    MinorVersion = cols[MONO_ASSEMBLY_MINOR_VERSION];
    BuildNumber = cols[MONO_ASSEMBLY_BUILD_NUMBER];
    RevNumber = cols[MONO_ASSEMBLY_REV_NUMBER];
    Flags = cols[MONO_ASSEMBLY_FLAGS];
    PublicKey = cols[MONO_ASSEMBLY_PUBLIC_KEY];
    Name = mono_metadata_string_heap (image,cols[MONO_ASSEMBLY_NAME]);
    Culture = mono_metadata_string_heap (image,cols[MONO_ASSEMBLY_CULTURE]);
  }
};

class File{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Flags;
  std::string Name;
  guint32 HashValue;

  File (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_FILE	  , MONO_FILE_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Flags = cols[MONO_FILE_FLAGS];
    Name = mono_metadata_string_heap (image,cols[MONO_FILE_NAME]);
    HashValue = cols[MONO_FILE_HASH_VALUE];
  } };
class GenericParam{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Number;
  unsigned int Flags;
  unsigned int Owner;
  std::string Name;

  GenericParam (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_GENERICPARAM	  , MONO_GENERICPARAM_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Number = cols[MONO_GENERICPARAM_NUMBER];
    Flags = cols[MONO_GENERICPARAM_FLAGS];
    Owner = cols[MONO_GENERICPARAM_OWNER];
    Name = mono_metadata_string_heap (image,cols[MONO_GENERICPARAM_NAME]);
  } };
class GenericParamConstraint{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Owner;
  unsigned int Constraint;

  GenericParamConstraint (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_GENERICPARAMCONSTRAINT	 , MONO_GENPARCONSTRAINT_SIZE);
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Owner = cols[MONO_GENPARCONSTRAINT_GENERICPAR];
    Constraint = cols[MONO_GENPARCONSTRAINT_CONSTRAINT];
  } };
class ImplMap{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Flags;
  unsigned int Member;
  std::string Name;
  unsigned int Scope;

  ImplMap (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_IMPLMAP	  , MONO_IMPLMAP_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Flags = cols[MONO_IMPLMAP_FLAGS];
    Member = cols[MONO_IMPLMAP_MEMBER];
    Name = mono_metadata_string_heap (image,cols[MONO_IMPLMAP_NAME]);
    Scope = cols[MONO_IMPLMAP_SCOPE];
  } };

class InterfaceImpl{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Class;
  unsigned int Interface;

  InterfaceImpl (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_INTERFACEIMPL	  , MONO_INTERFACEIMPL_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Class = cols[MONO_INTERFACEIMPL_CLASS];
    Interface = cols[MONO_INTERFACEIMPL_INTERFACE];
  } };

class MemberRef{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Class;
  std::string Name;
  guint32 Signature;

  MemberRef (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_MEMBERREF	  , MONO_MEMBERREF_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Class = cols[MONO_MEMBERREF_CLASS];
    Name = mono_metadata_string_heap (image,cols[MONO_MEMBERREF_NAME]);
    Signature = cols[MONO_MEMBERREF_SIGNATURE];
  } };

class MethodImpl{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Class;
  unsigned int Body;
  unsigned int Declaration;

  MethodImpl (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_METHODIMPL	  , MONO_METHODIMPL_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Class = cols[MONO_METHODIMPL_CLASS];
    Body = cols[MONO_METHODIMPL_BODY];
    Declaration = cols[MONO_METHODIMPL_DECLARATION];
  } };

class MethodSpec{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Method;
  guint32 Signature;

  MethodSpec (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_METHODSPEC	  , MONO_METHODSPEC_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Method = cols[MONO_METHODSPEC_METHOD];
    Signature = cols[MONO_METHODSPEC_SIGNATURE];
    const char* asd =  mono_metadata_blob_heap (image, Signature);
    const char *asd2;
    int sz = mono_metadata_decode_blob_size (asd, &asd2);
  } };

class MethodSemantics{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int  Semantics;
  unsigned int  Method;
  unsigned int  Association;

  MethodSemantics (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_METHODSEMANTICS , MONO_METHOD_SEMA_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Semantics = cols[MONO_METHOD_SEMA_SEMANTICS];
    Method = cols[MONO_METHOD_SEMA_METHOD];
    Association = cols[MONO_METHOD_SEMA_ASSOCIATION];
  } };


class Moduleref{
public:
  int myindex;
  MetaTable* TheTable;
  std::string Name;

  Moduleref (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_MODULEREF	  , MONO_MODULEREF_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Name = mono_metadata_string_heap (image,cols[MONO_MODULEREF_NAME]);
  } };

class Module{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int  Generation;
  std::string Name;
  unsigned int   Mvid;
  unsigned int   Enc;
  unsigned int   Encbase;

  Module (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_MODULE	  , MONO_MODULE_SIZE  );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Generation = cols[MONO_MODULE_GENERATION];
    Name = mono_metadata_string_heap (image,cols[MONO_MODULE_NAME]);
    Mvid = cols[MONO_MODULE_MVID];
    Enc = cols[MONO_MODULE_ENC];
    Encbase = cols[MONO_MODULE_ENCBASE];
  } };

class Param{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Flags;
  unsigned int Sequence;
  std::string Name;

  Param (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_PARAM	  , MONO_PARAM_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Flags = cols[MONO_PARAM_FLAGS];
    Sequence = cols[MONO_PARAM_SEQUENCE];
    Name = mono_metadata_string_heap (image,cols[MONO_PARAM_NAME]);
  } };

class Method{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Rva;
  unsigned int Implflags;
  unsigned int Flags;
  std::string Name;
  guint32 Signature;
  unsigned int Paramlist;
  MonoImage* img;
  Method (int iindex, MonoImage* image){
    img = image;
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_METHOD , MONO_METHOD_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Rva = cols[MONO_METHOD_RVA];
    Implflags = cols[MONO_METHOD_IMPLFLAGS];
    Flags = cols[MONO_METHOD_FLAGS];
    Name = mono_metadata_string_heap (image,cols[MONO_METHOD_NAME]);
    Signature = cols[MONO_METHOD_SIGNATURE];
    const char* asd =  mono_metadata_blob_heap (image, Signature);
    const char *asd2;
    int sz = mono_metadata_decode_blob_size (asd, &asd2);
    Paramlist = cols[MONO_METHOD_PARAMLIST];
  } 

  std::vector<Param* > * getParams(){
    guint32 *colsaux = TheTable->getRow(myindex+1);
    MetaTable* ParamTable=new MetaTable(img,MONO_TABLE_PARAM , MONO_PARAM_SIZE );
    int limit;
    std::vector<Param*> * aux = new std::vector<Param*> ();
    if (colsaux == NULL){
      limit = ParamTable->size;
    }else{
      limit = colsaux[MONO_METHOD_PARAMLIST];
    }
    for(int i=Paramlist;i<limit;i++){
      Param* maux=new Param(i,img);
      printf("\t\t%s\n",maux->Name.c_str());
      aux->push_back(maux);
    }
    return aux;
  }

};



class PropertyMap{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Parent;
  unsigned int PropertyList;

  PropertyMap (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_PROPERTYMAP	  , MONO_PROPERTY_MAP_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Parent = cols[MONO_PROPERTY_MAP_PARENT];
    PropertyList = cols[MONO_PROPERTY_MAP_PROPERTY_LIST];
  } };

class Property{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Flags;
  std::string Name;
  guint32 Type;

  Property (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_PROPERTY	  , MONO_PROPERTY_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Flags = cols[MONO_PROPERTY_FLAGS];
    Name = mono_metadata_string_heap (image,cols[MONO_PROPERTY_NAME]);
    Type = cols[MONO_PROPERTY_TYPE];
  } };

class TypeDef{
public:
  int myindex;
  MetaTable* TheTable;
  unsigned int Flags;
  std::string Name;
  std::string Namespace;
  unsigned int ExtendsIdx;
  unsigned int FieldListIdx;
  unsigned int MethodListIdx;
  MonoImage *img;
  TypeDef (int iindex, MonoImage* image){
    myindex=iindex;
    img=image;
    TheTable = new MetaTable(image,MONO_TABLE_TYPEDEF	  , MONO_TYPEDEF_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Flags = cols[MONO_TYPEDEF_FLAGS];
    Name = mono_metadata_string_heap (image,cols[MONO_TYPEDEF_NAME]);
    Namespace = mono_metadata_string_heap (image,cols[MONO_TYPEDEF_NAMESPACE]);
    ExtendsIdx = cols[MONO_TYPEDEF_EXTENDS];
    FieldListIdx = cols[MONO_TYPEDEF_FIELD_LIST];
    MethodListIdx = cols[MONO_TYPEDEF_METHOD_LIST];
  } 
  std::vector<Method*>* getMethods(){
    guint32 *colsaux = TheTable->getRow(myindex+1);
    MetaTable* MethodDefTable=new MetaTable(img,MONO_TABLE_METHOD , MONO_METHOD_SIZE );
    int limit;
    std::vector<Method*> * aux = new std::vector<Method*> ();
    if (colsaux == NULL){
      limit = MethodDefTable->size;
    }else{
      limit = colsaux[MONO_TYPEDEF_METHOD_LIST];
    }
    for(int i=MethodListIdx;i<limit;i++){
      Method* maux=new Method(i,img);
      printf("\t%s\n",maux->Name.c_str());
      aux->push_back(maux);
      maux->getParams();
    }
    return aux;
  }
};

class TypeSpec{
public:
  int myindex;
  MetaTable* TheTable;
  guint32 Signature;

  TypeSpec (int iindex, MonoImage* image){
    myindex=iindex;
    TheTable = new MetaTable(image,MONO_TABLE_TYPESPEC	 , MONO_TYPESPEC_SIZE );
    guint32 *cols;
    cols = TheTable->getRow(iindex);
    if(cols==NULL)
      return;
    Signature = cols[MONO_TYPESPEC_SIGNATURE];
  } 

};

}

//namespace Mono { namespace CIL {
//	class Param;
//	class Method;
//	class Module;
//	class Type;
//	class Field;
//	class Property;
//	class GenericParam;
//	class CILCustomAttribute;
//	class CILCustomAttributeHolder;
//
//	class CILCustomAttribute{
//		MonoCustomAttrEntry *attr;
//		Type * type;
//	public:
//		CILCustomAttribute(MonoCustomAttrEntry *att);
//		Type * getAttributeType();
//		//->Resolve()
//		Method * getConstructor();
//		//->Resolve()
//		bool hasConstructorArguments();
//		std::vector<Param*> * getConstructorArguments();
//		bool hasFields();
//		Field * getFields();
//		bool hasProperties();
//		std::vector<Property*> * getProperties();
//	};
//
//	class CILCustomAttributeHolder {
//		MonoCustomAttrInfo *cinfo;	
//	public:
//		CILCustomAttributeHolder(MonoCustomAttrInfo *attr);
//		std::vector<CILCustomAttribute*> *getAttributes(){
//			std::vector<CILCustomAttribute*> *attrvec = new std::vector<CILCustomAttribute*> ();
//			int sz = cinfo->num_attrs;
//			for(int i=0;i<sz;i++){
//				attrvec->push_back(new CILCustomAttribute(&cinfo->attrs[i]));
//			}
//			return attrvec;
//		}
//	};
//
//	class Type
//	{
//		//mono_metadata_token_index (class->type_token) - 1
//		//char *nname=mono_type_get_name(mt);
//		MonoClass* klass;
//		//mono_custom_attrs_from_class
//		MonoType * type;
//
//	public:
//		Type(MonoType* typ);
//		Type(MonoClass* typ);
//		std::string getName();
//		std::vector<Type*>* getInterfaces();
//		std::vector<Method*>* getMethods();
//		Module * getModule();
//		Type * getBaseType();
//		/*std::vector<Type*>* getFields(){
//			klass->fields
//		} */
//
//		bool isClass();
//		bool isInterface();
//		bool isValueType();
//		unsigned int getAttrs();
//
//		bool hasProperties();
//
//		std::vector<Property*>* getProperties();
//
//		std::vector<Field*>* getFields();
//
//		bool hasGenericParameters();
//
//		std::string getFullName(){
//			char *nname=mono_type_get_name(type);
//			return std::string(nname);
//		}	
//
//		std::vector<GenericParam*> * getGenericParameter();
//
//	};
//
//	class Field{
//		MonoClassField * field;
//	public:
//		Field(MonoClassField* f);
//		std::string getName();
//
//		Type* fieldType();
//
//		bool isStatic();
//
//		bool isPublic();
//		bool isAssembly();
//		bool isFamily();
//		bool isFamilyOrAssembly();
//		bool isFamilyAndAssembly();
//	};
//
//	class Property{
//		MonoProperty * prop;
//		MonoCustomAttrInfo *cinfo;
//		CILCustomAttributeHolder *ci;
//		//mono_custom_attrs_from_property
//	public:
//		Property(MonoProperty *p){
//			prop=p;
//			cinfo = mono_custom_attrs_from_property(prop->parent, prop);
//			ci = new CILCustomAttributeHolder(cinfo);
//		}
//		std::string getName();
//		Type* getPropertyType();
//		bool hasParameters();
//		std::vector<Param> getParameters();
//		Method * getMethod();
//		Method * setMethod();
//		bool getCustomAttributes();
//	};
//
//	class GenericParam {
//		MonoGenericParamFull * param;
//	public:
//		GenericParam (MonoGenericParamFull * gp){
//			param = gp;
//		}
//
//		std::string getName(){
//			MonoGenericParamInfo *aux;
//			std::string asd="";
//			asd+=param->info.name;
//			return asd;
//		}
//
//		Type* getType(){
//			MonoGenericParamInfo *aux;
//			//if(param->info.pklass){
//				//aux = &((MonoGenericParamFull *) param->owner)->info;
//			return new Type(param->info.pklass);
//			//}
//		}
//	};
//
//	bool Type::hasProperties(){
//		return mono_class_num_properties(klass) > 0;
//	}
//
//	std::vector<Property*>* Type::getProperties(){
//		unsigned int count = mono_class_num_properties(klass); // initializes properties if not initialized
//		std::vector<Property*> *p = new std::vector<Property*>();
//		for(int i=0; i< count; i++)
//			p->push_back(new Property(&klass->ext->properties[i]));
//		return p;
//	}
//
//	std::vector<Field*>* Type::getFields(){
//		int count = klass->field.count;
//		std::vector<Field*> *p = new std::vector<Field*>();
//		for(int i=0; i< count; i++)
//			p->push_back(new Field(&klass->fields[i]));
//		return p;
//	}
//
//	bool Type::hasGenericParameters(){
//		if (klass->generic_container==NULL)
//			return false;
//		return true;
//	}
//
//	std::vector<GenericParam*> * Type::getGenericParameter(){
//		std::vector<GenericParam*> *aux = new std::vector<GenericParam*>();
//		if(hasGenericParameters())
//			for(int i=0;i<klass->generic_container->type_argc;i++)
//				aux->push_back(new GenericParam(&klass->generic_container->type_params[i]));
//		return aux;
//	}
//
//	Field::Field(MonoClassField* f){
//		field=f;
//	}
//	std::string Field::getName(){
//		return std::string(field->name);
//	}
//
//	Type* Field::fieldType(){
//		return new Type(field ->type);
//	}
//
//	bool Field::isStatic(){
//		return field->type->attrs & MONO_FIELD_ATTR_STATIC;
//	}
//
//	bool Field::isPublic(){
//		return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_PUBLIC;
//	}
//	bool Field::isAssembly(){
//		return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_ASSEMBLY;
//	}
//	bool Field::isFamily(){
//		return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_FAMILY;
//	}
//	bool Field::isFamilyOrAssembly(){
//		return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_FAM_OR_ASSEM; 
//	}
//	bool Field::isFamilyAndAssembly(){
//		return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_FAM_AND_ASSEM; 
//	}
//
//	class Method
//	{
//		MonoMethod * method;
//		MonoCustomAttrInfo *cinfo;
//		CILCustomAttributeHolder *ci;
//		//mono_custom_attrs_from_method
//		unsigned int flags;
//		unsigned int iflags;
//
//		void getFlags(){
//			flags = mono_method_get_flags(method,&iflags);
//		}
//
//	public:
//		Method(MonoMethod *mthd);
//		std::vector<Param*>* getParams();
//		
//		std::string getName();
//
//		std::string getFullName(){
//			std::string name = "";
//			name += method->klass->name_space;
//			name += method->klass->name;
//			name += method->name;
//			return name;
//		}
//
//		bool isVarArgCall(){
//			return method->signature->call_convention == MONO_CALL_VARARG;
//		}
//
//		bool isDefaultCall(){
//			return method->signature->call_convention == MONO_CALL_DEFAULT;
//		}
//
//		bool isGenericCall(){
//			return (isVarArgCall() == isDefaultCall()) && isVarArgCall() == false;
//		}
//
//		Mono::CIL::Type* returnType(){
//			return new Mono::CIL::Type(method->signature->ret);
//		}
//
//		Mono::CIL::Type* declaringType(){
//			return new Mono::CIL::Type(method->klass);
//		}
//
//		bool isPublic(){
//			unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_PUBLIC);
//		}
//		bool isAssembly(){
//			unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_ASSEM);
//		}
//		bool isFamily(){
//			unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_FAMILY);
//		}
//		bool isFamilyOrAssembly(){
//			unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_FAM_OR_ASSEM);
//		}
//		bool isFamilyAndAssembly(){
//			unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_FAM_AND_ASSEM);
//		}
//
//		bool isConstructor(){
//			unsigned int CTOR_INVALID_FLAGS = (METHOD_ATTRIBUTE_STATIC);
//			unsigned int CTOR_REQUIRED_FLAGS = (METHOD_ATTRIBUTE_SPECIAL_NAME | METHOD_ATTRIBUTE_RT_SPECIAL_NAME);
//			return ((method->flags & CTOR_REQUIRED_FLAGS) == CTOR_REQUIRED_FLAGS &&
//					!(method->flags & CTOR_INVALID_FLAGS) &&
//					!strcmp (".ctor", method->name));
//		}
//
//		bool isGetter(){
//			unsigned int access = iflags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_FAM_AND_ASSEM);
//		}
//		bool isSetter(){
//			unsigned int access = iflags & MONO_METHOD_ATTR_ACCESS_MASK;
//			return (access == MONO_METHOD_ATTR_FAM_AND_ASSEM);
//		}
//
//		bool isStatic(){
//			unsigned int access = flags & MONO_METHOD_ATTR_STATIC;
//			return (access == MONO_METHOD_ATTR_STATIC);
//		}
//
//
//
//		//gpointer iter=NULL;
//		//MonoMethodSignature *mms = mono_method_signature(klass->methods[60]);
//		//MonoType *mt = mono_signature_get_params(mms,&iter);
//		//char *nname=mono_type_get_name(mt);
//	};
//
//	Type::Type(MonoType* typ){
//		type=typ;
//		char *nname=mono_type_get_name(type);
//		klass = mono_type_get_class(typ);		
//	}
//
//	Type::Type(MonoClass* typ){
//		klass=typ;
//		type = mono_class_get_type(typ);
//	}
//
//
//
//	class Param{
//		std::string name;
//		std::string type;
//		std::string typeNamespace;
//		Type *typeinfo;
//	public:
//		Param(std::string nm, Type *t){
//			typeinfo = t;
//			name = nm;
//		}
//
//		std::string getName(){
//			return name;
//		}
//
//		std::string getType(){
//			return typeinfo->getName();
//		}
//
//		Type * getTypeInfo(){
//			return typeinfo;
//		}
//
//		bool isIn(){
//			typeinfo->getAttrs() == MONO_PARAM_ATTR_IN;
//		}
//
//		bool isOut(){
//			typeinfo->getAttrs() == MONO_PARAM_ATTR_OUT;
//		}
//
//		bool isOptional(){
//			typeinfo->getAttrs() == MONO_PARAM_ATTR_OPTIONAL;
//		}
//
//		bool hasDefault(){
//			typeinfo->getAttrs() == MONO_PARAM_ATTR_HAS_DEFAULT;
//		}
//
//		bool hasFieldMarshal(){
//			typeinfo->getAttrs() == MONO_PARAM_ATTR_HAS_MARSHAL;
//		}
//
//		bool isUnused(){
//			typeinfo->getAttrs() == MONO_PARAM_ATTR_UNUSED;
//		}
//	};
//
//
//
//	Method::Method(MonoMethod *mthd){
//			method = mthd;
//			mono_method_signature(method);
//			mono_signature_get_return_type(method->signature);
//			cinfo = mono_custom_attrs_from_method(method);
//			ci = new CILCustomAttributeHolder(cinfo);
//			if (cinfo){
//				std::vector<CILCustomAttribute*>* asd = ci->getAttributes();
//				if(asd->size()) {
//					CILCustomAttribute *lol = asd->at(0);
//					bool q1 = lol->hasConstructorArguments();
//					bool q2 = lol->hasProperties();
//				}
//			}
//			getFlags();
//	}
//	std::vector<Param*>* Method::getParams(){
//		std::vector<Param*> *parms = new std::vector<Param*>();
//		gpointer* iter=0;
//		MonoMethodSignature *mms = mono_method_signature(method);
//		MonoType *mt = mono_signature_get_params(mms,(void**)&iter);
//		mono_signature_get_return_type(mms);
//		const char **names;
//		names = (const char**) malloc (sizeof(char*)*mms->param_count);
//		mono_method_get_param_names(method,names);
//		int i=0;
//		while(mt){
//			Mono::CIL::Param *paux = new Mono::CIL::Param(std::string(names[i++]),new Type(mt));
//			mt = mono_signature_get_params(mms,(void**)&iter);
//			parms->push_back(paux);
//		}
//		return parms;
//	}
//
//	std::string Method::getName(){
//		return std::string(method->name);
//	}
//
//	class Module
//	{
//		MonoImage* image;
//	public:
//		Module(MonoImage* img){
//			image=img;
//		}
//		//MonoClass * klass = mono_class_from_name_case (image, "System", "Console");
//		//Type* getType(std::string ){
//		//	std::vector<Type*> *taux = 
//		//	MonoType* type;
//		//	return new Type(type);
//		//}
//
//		Mono::CIL::Type* getType(std::string name){
//			unsigned int lastdot = name.find_last_of('.');
//
//			return new Mono::CIL::Type (mono_class_from_name_case (image, name.substr(0,lastdot).c_str(), name.substr(lastdot+1).c_str()));
//		}
//
//		Mono::CIL::Type* getType(std::string ns, std::string name){
//			return new Mono::CIL::Type (mono_class_from_name_case (image, ns.c_str(), name.c_str()));
//		}
//
//		std::vector<Type*>* getTypes(){
//			int index;	
//			std::vector<Type*> *typevec = new std::vector<Type*> ();
//			MonoTableInfo  *t = &image->tables [MONO_TABLE_TYPEDEF];
//			MonoError me;
//			for(int i=0;i<t->rows;i++){
////				MonoClass* mc = 
////				MonoType *mt = mono_class_get_type(mc);
//				Type *typaux = new Type(mono_class_get (image, MONO_TOKEN_TYPE_DEF | (i + 1)));
//				typevec->push_back(typaux);
//			}
//			return typevec;
//		}
//
//	};
//
//	std::string Type::getName(){
//		char *nname=mono_type_get_name(type);
//		return std::string(nname);
//	}
//
//	std::vector<Type*>* Type::getInterfaces(){
//		std::vector<Type*>* metvec = new std::vector<Type*>();
//		gpointer iter=NULL;
//		MonoClass * mm = mono_class_get_interfaces(klass,&iter);
//		while(mm){
//			Type *maux = new Type(mm);
//			metvec->push_back(maux);
//			mm = mono_class_get_interfaces(klass,&iter);
//		}
//		return metvec;
//	}
//
//	std::vector<Method*>* Type::getMethods(){
//		std::vector<Method*>* metvec = new std::vector<Method*>();
//		gpointer iter=NULL;
//		MonoMethod * mm = mono_class_get_methods(klass,&iter);
//		while(mm){
//			Method *maux = new Method(mm);
//			metvec->push_back(maux);
//			mm = mono_class_get_methods(klass,&iter);
//		}
//		return metvec;
//	}
//
//	Module * Type::getModule(){
//		return new Module(klass->image);
//	}
//
//	Type * Type::getBaseType(){
//		return new Type(klass->parent);
//	}
//
//	/*std::vector<Field*>* getFields(){
//		return new std::vector<Field*>(new Field());
//		
//	} */
//
//	bool Type::isClass(){
//		return (type->attrs & MONO_TYPE_ATTR_CLASS_SEMANTIC_MASK) == MONO_TYPE_ATTR_CLASS;
//	}
//
//	bool Type::isInterface(){
//		return (type->attrs & MONO_TYPE_ATTR_CLASS_SEMANTIC_MASK) == MONO_TYPE_ATTR_INTERFACE;
//	}
//
//	bool Type::isValueType(){
//		return 1==klass->valuetype;
//	}
//
//	unsigned int Type::getAttrs(){
//		return type->attrs;
//	}
//
//	class Assembly
//	{
//		//const char* pubkey =  mono_image_get_public_key(image,&size);
//		//guchar *token = (guchar*) malloc(sizeof(guchar)*size+1);
//		//mono_digest_get_public_token (token, (const guchar*)pubkey, size);
//		//gchar* encoded = encode_public_tok (token, 8);
//		////g_strlcpy ((char*)aname->public_key_token, encoded, MONO_PUBLIC_KEY_TOKEN_LENGTH);
//		MonoAssembly* assembly;
//	public:
//		Assembly(MonoAssembly* asmbly){
//			assembly = asmbly;
//		}
//
//		Assembly(std::string name){
//			MonoImageOpenStatus status;
//			mono_bool refonly = TRUE;
//			MonoAssembly* ma = mono_assembly_open(name.c_str(),&status);
//			if(ma!=NULL){
//				assembly = ma;
//			}
//		}
//
//		std::string getName(){
//			return std::string(assembly->aname.name);
//		}
//
//		bool hasPublicKey(){
//			assembly->aname.public_key ? true : false;
//		}
//
//		std::string getPublicKeyToken(){
//			char pubkey_token[MONO_PUBLIC_KEY_TOKEN_LENGTH+3];
//			memset(pubkey_token,0,MONO_PUBLIC_KEY_TOKEN_LENGTH+3);
//			memcpy (pubkey_token,(char*)(assembly->aname.public_key_token), MONO_PUBLIC_KEY_TOKEN_LENGTH*sizeof(char));
//			return std::string(pubkey_token);
//		}
//
//		Module* getMainModule(){ 
//			return new Module(assembly->image);
//		}
//
//		std::vector<Module*>* getModules(){
//			std::vector<Module*>* modvec;
//			return modvec;
//		}
//
//	};
//
//	std::string Property::getName(){
//		return std::string(prop->name);
//	}
//	Type* Property::getPropertyType(){
//		return ((new Method(prop->get))->returnType());
//	}
//	bool Property::hasParameters(){
//		return false;
//	}
//	std::vector<Param> Property::getParameters(){
//		return std::vector<Param>();
//	}
//	Method * Property::getMethod(){
//		return new Method(prop->get);
//	}
//	Method * Property::setMethod(){
//		return new Method(prop->set);
//	}
//	bool Property::getCustomAttributes(){
//		return prop->attrs == 0;
//	}
//
//	CILCustomAttributeHolder::CILCustomAttributeHolder(MonoCustomAttrInfo *attr){
//		cinfo = attr;
//		if(!cinfo) return;
//	}
//
//	CILCustomAttribute::CILCustomAttribute (MonoCustomAttrEntry * att){
//		attr=att;
//		type = new Type(att->ctor->klass);
//	}
//
//	Type * CILCustomAttribute::getAttributeType(){
//		return type;
//	}
//		//->Resolve()
//	Method * CILCustomAttribute::getConstructor(){
//		if(strcmp(attr->ctor->name,".ctor")==0)
//					return new Method(attr->ctor);
//		return NULL;
//	}
//	//->Resolve()
//	bool CILCustomAttribute::hasConstructorArguments(){
//		return getConstructor()->getParams()->size() > 0 ;
//	}
//
//	std::vector<Param*> * CILCustomAttribute::getConstructorArguments(){
//		//std::vector<Param*> *args = new std::vector<Param*>();
//		return getConstructor()->getParams();
//	}
//
//	bool CILCustomAttribute::hasFields(){return true;}
//	Field * CILCustomAttribute::getFields(){return NULL;}
//	bool CILCustomAttribute::hasProperties(){return type->hasProperties();}
//	std::vector<Property*> * CILCustomAttribute::getProperties(){return type->getProperties();}
//}}

namespace Mono { namespace CIL {
// AssemblyReader.h
class Param;
class Method;
class Module;
class Type;
class Field;
class Property;
class Assembly;
class GenericParam;
class CILCustomAttribute;
class CILCustomAttributeHolder;

class CILCustomAttribute{
  MonoCustomAttrEntry *attr;
  Type * type;
public:
  CILCustomAttribute(MonoCustomAttrEntry *att);
  Type * getAttributeType();
  //->Resolve()
  Method * getConstructor();
  //->Resolve()
  bool hasConstructorArguments();
  std::vector<Param*> * getConstructorArguments();
  bool hasFields();
  std::vector<Field*>* getFields();
  bool hasProperties();
  std::vector<Property*> * getProperties();
};

class CILCustomAttributeHolder {
  MonoCustomAttrInfo *cinfo;	
public:
  CILCustomAttributeHolder(MonoCustomAttrInfo *attr);
  std::vector<CILCustomAttribute*> *getAttributes();
};

class Type
{
  //mono_metadata_token_index (class->type_token) - 1
  //char *nname=mono_type_get_name(mt);
  MonoClass* klass;
  char* nname;
  //mono_custom_attrs_from_class
  MonoType * type;
  bool genericparamq;
  std::vector<Property*> *propmethods;
  void setGetterSetter(Method * maux);
  
public:
  bool hasClass(){
    return klass;
  }
  
  bool hasGenericClass(){
    if(hasClass())
      if(klass->generic_class)
        return true;
    return false;
  }

  Type * getGenericClass(){
    if(hasGenericClass())
	  return new Type(klass->generic_class->container_class);
	return this; 
  }
  
  unsigned int getMetadataToken(){
    return klass->type_token;
  }
  Type(MonoType* typ);
  Type(MonoClass* typ);
  Type(MonoType* typ, bool genericparam);
  Type(MonoClass* typ, bool genericparam);
  std::string getName();
  std::string getNamespace();
  std::vector<Type*>* getInterfaces();
  std::vector<Method*>* getMethods();
  Module * getModule();
  Type * getBaseType();
  /*std::vector<Type*>* getFields(){
    klass->fields
    } */
  bool isClass();
  bool isInterface();
  bool isValueType();
  bool isArray();
  bool isGenericInstance();
  bool isGenericParameter();
  Type* getArrayType();
  unsigned int getArrayRank();
  unsigned int getAttrs();
  bool hasProperties();
  std::vector<Property*>* getProperties();
  std::vector<Field*>* getFields();
  bool hasGenericParameters();
  std::string getFullName();
  std::vector<GenericParam*> * getGenericParameter();
};

class Field{
  MonoClassField * field;
public:
  Field(MonoClassField* f);
  std::string getName();
  Type* fieldType();
  bool isStatic();
  bool isPublic();
  bool isAssembly();
  bool isFamily();
  bool isFamilyOrAssembly();
  bool isFamilyAndAssembly();
};

class Property{
  MonoProperty * prop;
  MonoCustomAttrInfo *cinfo;
  CILCustomAttributeHolder *ci;
  //mono_custom_attrs_from_property
public:
  Property(MonoProperty *p);
  std::string getName();
  Type* getPropertyType();
  bool hasParameters();
  std::vector<Param*>* getParameters();
  Method * getMethod();
  Method * setMethod();
  CILCustomAttributeHolder * getCustomAttributes();
};

class GenericParam {
  MonoGenericParamFull * param;
public:
  GenericParam (MonoGenericParamFull * gp);
  std::string getName();
  bool isTypeParameter();
  bool isMethodParameter();
  Type* getType();
};

class Param{
  std::string name;
  std::string type;
  std::string typeNamespace;
  Type *typeinfo;
  unsigned int idx;
  MonoMethod * parentM;
public:
  Param(std::string nm, Type *t,unsigned int idx, MonoMethod* parentm);
  std::string getName();
  std::string getType();
  Type * getTypeInfo();
  bool isIn();
  bool isOut();
  bool isOptional();
  bool hasDefault();
  unsigned int getIdx();
  bool hasFieldMarshal();
  bool isUnused();
  CILCustomAttributeHolder* getCustomAttributes();
};

class Method
{
  
  MonoCustomAttrInfo *cinfo;
  CILCustomAttributeHolder *ci;
  //mono_custom_attrs_from_method
  unsigned int flags;
  unsigned int iflags;
  bool issetter;
  bool isgetter;
  void getFlags(){
    flags = mono_method_get_flags(method,&iflags);
  }
  
public:
  //FIXME!!
  bool equal(Method* tocmpr);
  MonoMethod * method;
  //FIXME!!
  unsigned int MetadataToken(){
    return method->token;
  }
  bool isSetter(){
    return issetter;
  }
  bool isGetter(){
    return isgetter;
  }
  void isSetter(bool val){
    issetter=val;
  }
  void isGetter(bool val){
    isgetter = val;
  }
  
  bool isNull(){
    return method==NULL;
  }
  
  CILCustomAttributeHolder* getCustomAttributes();
  
  Method(MonoMethod *mthd);
  std::vector<Param*>* getParams();
  std::string getName();
  std::string getFullName();
  bool isVarArgCall();
  bool isDefaultCall();
  bool isGenericCall();
  bool hasParameters();
  Mono::CIL::Type* returnType();
  Mono::CIL::Type* declaringType();
  bool isPublic();
  bool isAssembly();
  bool isFamily();
  bool isFamilyOrAssembly();
  bool isFamilyAndAssembly();
  bool isConstructor();
  bool isStatic();
};


class Module
{
  MonoImage* image;
public:
  Module(MonoImage* img);
  Mono::CIL::Type* getType(std::string name);
  Mono::CIL::Type* getType(std::string ns, std::string name);
  std::vector<Type*>* getTypes();
  Mono::CIL::Assembly* getAssembly();
};

class Assembly
{
  MonoAssembly* assembly;
public:
  Assembly(MonoAssembly* asmbly);
  Assembly(std::string name);
  std::string getName();
  bool hasPublicKey();
  std::string getPublicKeyToken();
  Module* getMainModule();
  std::vector<Module*>* getModules();
};
// EO AssemblyReader.h

// assembly definition
Assembly::Assembly(MonoAssembly* asmbly){
  assembly = asmbly;
}

Assembly::Assembly(std::string name){
  MonoImageOpenStatus status;
  mono_bool refonly = TRUE;
  MonoAssembly* ma = mono_assembly_open(name.c_str(),&status);
  if(ma!=NULL){
    assembly = ma;
  }
}

std::string Assembly::getName(){
  return std::string(assembly->aname.name);
}

bool Assembly::hasPublicKey(){
  return assembly->aname.public_key ? true : false;
}

std::string Assembly::getPublicKeyToken(){
  char pubkey_token[MONO_PUBLIC_KEY_TOKEN_LENGTH+3];
  memset(pubkey_token,0,MONO_PUBLIC_KEY_TOKEN_LENGTH+3);
  memcpy (pubkey_token,(char*)(assembly->aname.public_key_token), MONO_PUBLIC_KEY_TOKEN_LENGTH*sizeof(char));
  return std::string(pubkey_token);
}

Module* Assembly::getMainModule(){ 
  return new Module(assembly->image);
}

std::vector<Module*>* Assembly::getModules(){
  std::vector<Module*>* modvec;
  return modvec;
}
// eo assembly definition
// module definition
Module::Module(MonoImage* img){
  image=img;
}

Mono::CIL::Type* Module::getType(std::string name){
  unsigned int lastdot = name.find_last_of('.');
  
  return new Mono::CIL::Type (mono_class_from_name_case (image, name.substr(0,lastdot).c_str(), name.substr(lastdot+1).c_str()));
}

Assembly* Module::getAssembly(){
  return new Mono::CIL::Assembly(image->assembly);
}

Mono::CIL::Type* Module::getType(std::string ns, std::string name){
  return new Mono::CIL::Type (mono_class_from_name_case (image, ns.c_str(), name.c_str()));
}

std::vector<Type*>* Module::getTypes(){
  int index;	
  std::vector<Type*> *typevec = new std::vector<Type*> ();
  MonoTableInfo  *t = &image->tables [MONO_TABLE_TYPEDEF];
  MonoError me;
  for(int i=0;i<t->rows;i++){
    //				MonoClass* mc = 
    //				MonoType *mt = mono_class_get_type(mc);
    Type *typaux = new Type(mono_class_get (image, MONO_TOKEN_TYPE_DEF | (i + 1)));
    typevec->push_back(typaux);
  }
  return typevec;
}

// eo module definition
// method definitions




Method::Method(MonoMethod *mthd){
  method = mthd;
  if(method == NULL)
    return;
  issetter = isgetter = false;
  mono_method_signature(method);
  mono_signature_get_return_type(method->signature);
  cinfo = mono_custom_attrs_from_method(method);
  ci = new CILCustomAttributeHolder(cinfo);
  if (cinfo){
    std::vector<CILCustomAttribute*>* asd = ci->getAttributes();
    if(asd->size()) {
      CILCustomAttribute *lol = asd->at(0);
      bool q1 = lol->hasConstructorArguments();
      bool q2 = lol->hasProperties();
    }
  }
  getFlags();
}

CILCustomAttributeHolder * Method::getCustomAttributes(){
  return ci;
}

bool Method::hasParameters(){
  if(!method) return false;
  return mono_signature_get_param_count(method->signature) > 0;
}

bool Method::equal(Method* tocmpr){
  if(tocmpr->method==NULL || !method) return false;
  return mono_metadata_signature_equal (mono_method_signature (method), mono_method_signature (tocmpr->method));
}

std::vector<Param*>* Method::getParams(){
  std::vector<Param*> *parms = new std::vector<Param*>();
  if(!method) return parms;
  gpointer* iter=0;
  MonoMethodSignature *mms = mono_method_signature(method);
  MonoType *mt = mono_signature_get_params(mms,(void**)&iter);
  mono_signature_get_return_type(mms);
  const char **names;
  names = (const char**) malloc (sizeof(char*)*mms->param_count);
  mono_method_get_param_names(method,names);
  int i=0;
  while(mt){
    Mono::CIL::Param *paux = new Mono::CIL::Param(std::string(names[i]),new Type(mt),i,method);
    mt = mono_signature_get_params(mms,(void**)&iter);
    parms->push_back(paux);
    i++;
  }
  return parms;
}

std::string Method::getName(){
  return std::string(method->name);
}

std::string Method::getFullName(){
  std::string name = "";
  name += method->klass->name_space;
  name += ".";
  name += method->klass->name;
  name += ".";
  name += method->name;
  return name;
}

bool Method::isVarArgCall(){
  return method->signature->call_convention == MONO_CALL_VARARG;
}

bool Method::isDefaultCall(){
  return method->signature->call_convention == MONO_CALL_DEFAULT;
}

bool Method::isGenericCall(){
  return (isVarArgCall() == isDefaultCall()) && isVarArgCall() == false;
}

Mono::CIL::Type* Method::returnType(){
  return new Mono::CIL::Type(method->signature->ret);
}

Mono::CIL::Type* Method::declaringType(){
  return new Mono::CIL::Type(method->klass);
}

bool Method::isPublic(){
  unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
  return (access == MONO_METHOD_ATTR_PUBLIC);
}
bool Method::isAssembly(){
  unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
  return (access == MONO_METHOD_ATTR_ASSEM);
}
bool Method::isFamily(){
  unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
  return (access == MONO_METHOD_ATTR_FAMILY);
}
bool Method::isFamilyOrAssembly(){
  unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
  return (access == MONO_METHOD_ATTR_FAM_OR_ASSEM);
}
bool Method::isFamilyAndAssembly(){
  unsigned int access = flags & MONO_METHOD_ATTR_ACCESS_MASK;
  return (access == MONO_METHOD_ATTR_FAM_AND_ASSEM);
}

bool Method::isConstructor(){
  unsigned int CTOR_INVALID_FLAGS = (METHOD_ATTRIBUTE_STATIC);
  unsigned int CTOR_REQUIRED_FLAGS = (METHOD_ATTRIBUTE_SPECIAL_NAME | METHOD_ATTRIBUTE_RT_SPECIAL_NAME);
  return ((method->flags & CTOR_REQUIRED_FLAGS) == CTOR_REQUIRED_FLAGS &&
          !(method->flags & CTOR_INVALID_FLAGS) &&
          !strcmp (".ctor", method->name));
}

bool Method::isStatic(){
  unsigned int access = flags & MONO_METHOD_ATTR_STATIC;
  return (access == MONO_METHOD_ATTR_STATIC);
}

// eo method definitions

// type definitions



Type::Type(MonoClass* typ){
  propmethods = NULL;
  genericparamq = false;
  klass=typ;
  type = mono_class_get_type(typ);
//		klass = mono_type_get_class(type);
//		if(!klass)
//			klass = mono_class_from_mono_type(type);
//		nname=mono_type_get_name(type);
  getProperties();
}

Type::Type(MonoType* typ){
  klass=NULL;
  propmethods = NULL;
  genericparamq = false;
  type=typ;
  nname=mono_type_get_name(type);
  switch(typ->type){
  case MonoTypeEnum::MONO_TYPE_PTR:
    klass = mono_type_get_class(typ->data.type);
    break;
  case MonoTypeEnum::MONO_TYPE_GENERICINST:
    if(typ->data.generic_class->cached_class)
      klass = typ->data.generic_class->cached_class;
    else
      klass = typ->data.generic_class->container_class;
    break;
  case MonoTypeEnum::MONO_TYPE_MVAR:
  case MonoTypeEnum::MONO_TYPE_VAR:
    break;
  case MonoTypeEnum::MONO_TYPE_ARRAY:
  case MonoTypeEnum::MONO_TYPE_SZARRAY:
    klass = mono_class_from_mono_type(typ);
    //klass = typ->data.array->eklass;
    break;
  default:
    klass = mono_type_get_class(typ);
    if(!klass)
      klass = mono_class_from_mono_type(typ);
    //klass = mono_type_get_class(typ);
  }
  if(klass)
    getProperties();
}

Type::Type(MonoType* typ, bool gp){
  klass=NULL;
  propmethods = NULL;
  genericparamq = gp;
  type=typ;
  nname=mono_type_get_name(type);
  switch(typ->type){
  case MonoTypeEnum::MONO_TYPE_PTR:
    klass = mono_type_get_class(typ->data.type);
    break;
  case MonoTypeEnum::MONO_TYPE_GENERICINST:
    if(typ->data.generic_class->cached_class)
      klass = typ->data.generic_class->cached_class;
    else
      klass = typ->data.generic_class->container_class;
    break;
  case MonoTypeEnum::MONO_TYPE_MVAR:
  case MonoTypeEnum::MONO_TYPE_VAR:
    break;
  case MonoTypeEnum::MONO_TYPE_ARRAY:
  case MonoTypeEnum::MONO_TYPE_SZARRAY:
    //			klass = typ->data.array->eklass;
    //			break;
  default:
    klass = mono_type_get_class(typ);
    if(!klass)
      klass = mono_class_from_mono_type(typ);
  }
  if(klass)
    getProperties();
}

Type::Type(MonoClass* typ, bool gp){
  propmethods = NULL;
  genericparamq = gp;
  klass=typ;
  type = mono_class_get_type(typ);
  getProperties();
}

bool Type::hasProperties(){
  return mono_class_num_properties(klass) > 0;
}

bool Type::isArray(){
  return type->type == MonoTypeEnum::MONO_TYPE_ARRAY || type->type == MonoTypeEnum::MONO_TYPE_SZARRAY;
}
bool Type::isGenericInstance(){
  return type->type == MonoTypeEnum::MONO_TYPE_GENERICINST;
}
bool Type::isGenericParameter(){
	return type->type == MonoTypeEnum::MONO_TYPE_VAR ||  type->type == MonoTypeEnum::MONO_TYPE_MVAR; // needs to be set during construction!
}

Type* Type::getArrayType(){
  return new Type(type->data.array->eklass);
}

unsigned int Type::getArrayRank(){
  if(hasClass())
    return klass->rank;
  return type->data.array->rank;
}

std::vector<Property*>* Type::getProperties(){
  if(propmethods) return propmethods;
  unsigned int count = mono_class_num_properties(klass); // initializes properties if not initialized
  std::vector<Property*> *p = new std::vector<Property*>();
  for(int i=0; i< count; i++)
    p->push_back(new Property(&klass->ext->properties[i]));
  propmethods = p;
  return p;
}

std::vector<Field*>* Type::getFields(){
  int count = klass->field.count;
  std::vector<Field*> *p = new std::vector<Field*>();
  for(int i=0; i< count; i++)
    p->push_back(new Field(&klass->fields[i]));
  return p;
}

bool Type::hasGenericParameters(){
  if(klass->generic_container != NULL) {
    return true;
  }// if type is generic instantiation we need to check for the generic class!
  // however, the test above should take care of things if the initialization was 
  // made with a monotype (the pointer is already set)
  if(type->type == MONO_TYPE_GENERICINST){
    if(klass->generic_class==NULL) return false;
    if(klass->generic_class->container_class->generic_container!=NULL)
      return true;
  }/*else{
     if (klass->generic_container==NULL)
     return false;
     }*/
  return false;
}

std::vector<GenericParam*> * Type::getGenericParameter(){
  std::vector<GenericParam*> *aux = new std::vector<GenericParam*>();
  MonoClass *ptr = klass;
  if(!hasGenericParameters()) return aux;
  if(type->type == MONO_TYPE_GENERICINST && klass->generic_class !=NULL) ptr = klass->generic_class->container_class;
  for(int i=0;i<ptr->generic_container->type_argc;i++){
    aux->push_back(new GenericParam(&ptr->generic_container->type_params[i]));
  }
  return aux;
}

std::string Type::getName(){
  if(hasClass())
    return std::string(klass->name);
  std::string name(mono_type_get_name(type));
  unsigned int lastdot = name.find_last_of('.');
  
  return name.substr(lastdot+1).c_str();
  //return std::string(nname);
}

std::string Type::getNamespace(){
  if(hasClass())
    return std::string(klass->name_space);
  std::string name(mono_type_get_name(type));
  unsigned int lastdot = name.find_last_of('.');
  
  return name.substr(0,lastdot).c_str();
  //return std::string(nname);
}

std::string Type::getFullName(){
  if(hasClass()){
    return getNamespace()+"."+getName();
  }
  char *nname=mono_type_get_name(type);
  return std::string(nname);
}	

std::vector<Type*>* Type::getInterfaces(){
  std::vector<Type*>* metvec = new std::vector<Type*>();
  gpointer iter=NULL;
  MonoClass * mm = mono_class_get_interfaces(klass,&iter);
  while(mm){
    Type *maux = new Type(mm);
    metvec->push_back(maux);
    mm = mono_class_get_interfaces(klass,&iter);
  }
  return metvec;
}



std::vector<Method*>* Type::getMethods(){
  std::vector<Method*>* metvec = new std::vector<Method*>();
  gpointer iter=NULL;
  MonoMethod * mm = mono_class_get_methods(klass,&iter);
  getProperties();
  while(mm){
    Method *maux = new Method(mm);
    metvec->push_back(maux);
    setGetterSetter(maux);
    mm = mono_class_get_methods(klass,&iter);
  }
  return metvec;
}

Module * Type::getModule(){
  return new Module(klass->image);
}

Type * Type::getBaseType(){
  if(klass->parent==NULL) return NULL;
  return new Type(klass->parent);
}

/*std::vector<Field*>* getFields(){
  return new std::vector<Field*>(new Field());
  
  } */

bool Type::isClass(){
  return (type->attrs & MONO_TYPE_ATTR_CLASS_SEMANTIC_MASK) == MONO_TYPE_ATTR_CLASS;
}

bool Type::isInterface(){
//		#define MONO_CLASS_IS_INTERFACE(c) ((c->flags & TYPE_ATTRIBUTE_INTERFACE) || (c->byval_arg.type == MONO_TYPE_VAR) || (c->byval_arg.type == MONO_TYPE_MVAR))
  if(hasClass())
    return MONO_CLASS_IS_INTERFACE(klass);
  return (type->attrs & MONO_TYPE_ATTR_CLASS_SEMANTIC_MASK) == MONO_TYPE_ATTR_INTERFACE;
}

bool Type::isValueType(){
  return 1==klass->valuetype;
}

void Type::setGetterSetter(Method * maux){
  for(int i=0;i<propmethods->size();i++){
    if(maux->equal(propmethods->at(i)->getMethod()))
      maux->isGetter(true);
    if(maux->equal(propmethods->at(i)->setMethod()))
      maux->isSetter(true);
  }
}

unsigned int Type::getAttrs(){
  return type->attrs;
}

// eo type definitions
// field definitions
Field::Field(MonoClassField* f){
  field=f;
}
std::string Field::getName(){
  return std::string(field->name);
}

Type* Field::fieldType(){
  return new Type(field ->type);
}

bool Field::isStatic(){
  return field->type->attrs & MONO_FIELD_ATTR_STATIC;
}

bool Field::isPublic(){
  return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_PUBLIC;
}
bool Field::isAssembly(){
  return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_ASSEMBLY;
}
bool Field::isFamily(){
  return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_FAMILY;
}
bool Field::isFamilyOrAssembly(){
  return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_FAM_OR_ASSEM; 
}
bool Field::isFamilyAndAssembly(){
  return (field->type->attrs & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) == MONO_FIELD_ATTR_FAM_AND_ASSEM; 
}  
// eo field definitions
// property definitions

Property::Property(MonoProperty *p){
  prop=p;
  cinfo = mono_custom_attrs_from_property(prop->parent, prop);
  ci = new CILCustomAttributeHolder(cinfo);
}

std::string Property::getName(){
  return std::string(prop->name);
}
Type* Property::getPropertyType(){
  if(prop->get!=NULL)
    return ((Method(prop->get)).returnType());
  if(prop->set!=NULL)
    return ((Method(prop->set)).returnType());
}
bool Property::hasParameters(){
  return (Method(prop->get).hasParameters() || Method(prop->set).hasParameters());
}
std::vector<Param*>* Property::getParameters(){
  std::vector<Param*> *parvec; 
  if (!hasParameters())
    return new std::vector<Param*>();
  parvec = Method(prop->get).getParams();
  std::vector<Param*> *parvec2 = Method(prop->set).getParams();
  for(int i=0; i< parvec2->size();i++)
    parvec->push_back(parvec2->at(i));
  return parvec;
}
Method * Property::getMethod(){
  return new Method(prop->get);
}
Method * Property::setMethod(){
  return new Method(prop->set);
}
CILCustomAttributeHolder* Property::getCustomAttributes(){
  return new CILCustomAttributeHolder(   mono_custom_attrs_from_property (prop->parent,prop));
}

// CILCustomAttributeHolder definitions
std::vector<CILCustomAttribute*> *CILCustomAttributeHolder::getAttributes(){
  std::vector<CILCustomAttribute*> *attrvec = new std::vector<CILCustomAttribute*> ();
  if(!cinfo) return attrvec;
  int sz = cinfo->num_attrs;
  for(int i=0;i<sz;i++){
    attrvec->push_back(new CILCustomAttribute(&cinfo->attrs[i]));
  }
  return attrvec;
}

CILCustomAttributeHolder::CILCustomAttributeHolder(MonoCustomAttrInfo *attr){
  cinfo = attr;
  if(!cinfo) return;
}
// eo CILCustomAttributeHolder definitions

// CILCustomAttribute definitions

CILCustomAttribute::CILCustomAttribute (MonoCustomAttrEntry * att){
  attr=att;
  type = new Type(att->ctor->klass);
}

Type * CILCustomAttribute::getAttributeType(){
  return type;
}
//->Resolve()
Method * CILCustomAttribute::getConstructor(){
  if(strcmp(attr->ctor->name,".ctor")==0)
    return new Method(attr->ctor);
  return NULL;
}
//->Resolve()
bool CILCustomAttribute::hasConstructorArguments(){
  return getConstructor()->getParams()->size() > 0 ;
}

std::vector<Param*> * CILCustomAttribute::getConstructorArguments(){
  //std::vector<Param*> *args = new std::vector<Param*>();
  return getConstructor()->getParams();
}

bool CILCustomAttribute::hasProperties(){return type->hasProperties();}
std::vector<Property*> * CILCustomAttribute::getProperties(){return type->getProperties();}

bool CILCustomAttribute::hasFields(){return type->getFields()->size()>0;}
std::vector<Field *>* CILCustomAttribute::getFields(){return type->getFields();}
// eo CILCustomAttribute definitions

// generic param definitions
GenericParam::GenericParam (MonoGenericParamFull * gp){
  param = gp;
}

std::string GenericParam::getName(){
  MonoGenericParamInfo *aux;
  std::string asd="";
  asd+=param->info.name;
  return asd;
}

Type* GenericParam::getType(){
  MonoGenericParamInfo *aux;
  //if(param->info.pklass){
  //aux = &((MonoGenericParamFull *) param->owner)->info;
  return new Type(param->info.pklass, true);
  //}
}

bool GenericParam::isTypeParameter(){
  return param->param.owner->is_method == 0;
}

bool GenericParam::isMethodParameter(){
  return param->param.owner->is_method == 1;
}
// param definitions

Param::Param(std::string nm, Type *t, unsigned int ix, MonoMethod *par){
  typeinfo = t;
  name = nm;
  idx = ix;
  parentM = par;
}

std::string Param::getName(){
  return name;
}

std::string Param::getType(){
  return typeinfo->getName();
}

Type * Param::getTypeInfo(){
  return typeinfo;
}

bool Param::isIn(){
  return typeinfo->getAttrs() == MONO_PARAM_ATTR_IN;
}

bool Param::isOut(){
  return  typeinfo->getAttrs() == MONO_PARAM_ATTR_OUT;
}

bool Param::isOptional(){
  return  typeinfo->getAttrs() == MONO_PARAM_ATTR_OPTIONAL;
}

bool Param::hasDefault(){
  return  typeinfo->getAttrs() == MONO_PARAM_ATTR_HAS_DEFAULT;
}

unsigned int Param::getIdx(){
  return idx;
}

bool Param::hasFieldMarshal(){
  return  typeinfo->getAttrs() == MONO_PARAM_ATTR_HAS_MARSHAL;
}

bool Param::isUnused(){
  return  typeinfo->getAttrs() == MONO_PARAM_ATTR_UNUSED;
}

CILCustomAttributeHolder* Param::getCustomAttributes(){
  return new CILCustomAttributeHolder( mono_custom_attrs_from_param(parentM,idx+1));
}

}}

static gchar*
encode_public_tok (const guchar *token, gint32 len)
{
  const static gchar allowed [] = { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' };
  gchar *res;
  int i;
  
  res = (gchar*) malloc (len * 2 + 1);
  for (i = 0; i < len; i++) {
    res [i * 2] = allowed [token [i] >> 4];
    res [i * 2 + 1] = allowed [token [i] & 0xF];
  }
  res [len * 2] = 0;
  return res;
}
using namespace DllImport;
using namespace Mono::CIL;
std::vector<std::string> * DumpAssemblyRefs (std::string name)
{	
  Mono::CIL::Assembly *mca = new Mono::CIL::Assembly(name);
  const char * cname = name.c_str();
  gpointer iter=NULL;
  Mono::CIL::Module *	mcm = mca->getMainModule(); 
  //System.IComparable`1
  //"System.Collections.Generic","Dictionary`2"
  //System.Collections.Generic.IList`1
  
  //Mono::CIL::Type *mcc = mcm->getType("System.Runtime.Serialization","StreamingContext");
  //Mono::CIL::Type *mcc = mcm->getType("System.Runtime.InteropServices","ComVisibleAttribute");
  Mono::CIL::Type *mcc = mcm->getType("System.Text","StringBuilder");
  
  bool lol = mcc->hasGenericParameters();
  bool lol1 = mcc->isValueType();
  bool lol3 = mcc->hasGenericParameters();
  std::vector<Mono::CIL::GenericParam*>*a = mcc->getGenericParameter();
  if(a->size())
    std::string asds = (*a)[0]->getName();
  bool lol2 = mcc->hasProperties();
  std::vector<Mono::CIL::Type*> *interfaces = mcc->getInterfaces();
  mcc->getProperties();
  std::vector<Mono::CIL::Method*> *metvec = mcc->getMethods();
  std::vector<Mono::CIL::Method*> *metvec2 = new std::vector<Mono::CIL::Method*> ();
  for(int i=0;i<metvec->size();i++){
    std::string fullname = metvec->at(i)->getFullName();
    std::string name= metvec->at(i)->getName();
    if(name.find("AppendFormat")!=std::string::npos)
      metvec2->push_back(metvec->at(i));
  }
  std::vector<Mono::CIL::Param*> *parvec;
  for(int i=0;i<metvec2->size();i++){
	  parvec=metvec2->at(i)->getParams();
	  new Mono::CIL::Method(metvec2->at(i)->method);
  }
  std::vector<Mono::CIL::Type*> *asd = mcm->getTypes();
  std::vector<std::string> * names = new std::vector<std::string>();
  for(int i=0;i<asd->size();i++){
    names->push_back((*asd)[i]->getName());
    (*asd)[i]->getMethods();
    (*asd)[i]->getProperties();
  }
  return names;
  
  //for(int i=0;i<asd->size();i++)
  //	printf("%s\n",(*asd)[i]->getName().c_str());
  //for(int i=0; i<metvec->size();i++)
  //{
  //	printf("%s - ",(*metvec)[i]->isPublic()?"p ":"np");
  //	printf("%s\n",(*metvec)[i]->getName().c_str());
  //	std::vector<Mono::CIL::Param*> *parvec = (*metvec)[i]->getParams();
  //	for (int j = 0; j< parvec->size(); j++ )
  //		printf("\t%s %s\n",(*parvec)[j]->getType().c_str(),(*parvec)[j]->getName().c_str());
  //}
  //std::vector<Mono::CIL::Type*> *itfcvec = mcc->getInterfaces();
  //for(int i=0; i<itfcvec->size();i++)
  //{
  //	printf("%s\n",(*itfcvec)[i]->getName().c_str());
  //}
  
  //MethodSpec *ms;
  //TypeDef *td;
  //GenericParam *gp;
  //for (unsigned int i = 0; i < 10000 ; i++){
  //td= new TypeDef(i,image);
  //	ms= new MethodSpec(i,image);
  //	gp= new GenericParam(i,image);
  //if(td->Name.size()==0)
  //	break;
  //printf("%s ",td->Name.c_str());
  ////if(td->Namespace)
  //printf("-- %s\n",td->Namespace.c_str());
  //	//else
  //	printf("-- gp%s\n",gp->Name.c_str());
  //	
  //	td->getMethods();
  //}
}


namespace clang {
using namespace sema;

using namespace clix;

/*
 * Dumps a few fields from the AssemblyRef table
 */

unsigned int decodeRow(unsigned int codedrow, unsigned int * code, unsigned int bits){
  unsigned int bitmask =0;
  for(int i=0; i<bits; i++){
    bitmask<<1; bitmask|=1;
  }
  unsigned int codeaux=codedrow & bitmask;
  unsigned int row=codedrow>>bits;
  *code=codeaux;
  return row;
}



static IdentifierInfo *getIdentifier(Sema &S, StringRef Name) {
  IdentifierTable& IdentTable = S.getPreprocessor().getIdentifierTable();
  return &IdentTable.get(Name);
}

static IdentifierInfo *getIdentifier(Sema &S, System::String ^Name) {
  std::string IdentName = marshalString<E_UTF8>(Name);
  return getIdentifier(S, IdentName);
}

static NamespaceDecl *findCreateNamespace(Sema &S, DeclContext *DC,
                                          StringRef Namespace) {
  IdentifierInfo *II = getIdentifier(S, Namespace);
  DeclContextLookupResult Res = DC->lookup(DeclarationName(II));
  
  for (auto it = Res.begin(); it != Res.end(); ++it) {
    if (NamespaceDecl *ND = dyn_cast<NamespaceDecl>(*it)) {
      return ND;
    }
  }
  
  NamespaceDecl *NS = NamespaceDecl::Create(S.getASTContext(), DC,
                                            /*IsInline=*/false, SourceLocation(), SourceLocation(), II, 0);
  DC->addDecl(NS);
  return NS;
}

static DeclContext *findCreateNamespaces(Sema &S, StringRef Namespace) {
  TranslationUnitDecl* TU = S.getASTContext().getTranslationUnitDecl();
  DeclContext* DC = TU->getPrimaryContext();
  
  if (Namespace.size() == 0)
    return DC;
  
  llvm::SmallVector<StringRef, 4> Namespaces;
  llvm::SplitString(Namespace, Namespaces, ".");
  
  NamespaceDecl* NS = 0;
  for (unsigned i = 0; i < Namespaces.size(); ++i) {
    NS = findCreateNamespace(S, DC, Namespaces[i]);
    assert(NS && "Expected a valid namespace");
    DC = NS->getPrimaryContext();
  }
  
  return NS;
}

static DeclContext *findCreateNamespaces(Sema &S, 
                                         //TypeReference ^Type
                                         Mono::CIL::Type* Type) {
  std::string Namespace = /*marshalString<E_UTF8>*/Type->getNamespace();
  return findCreateNamespaces(S, Namespace);
}

//static DeclContext* findCreateNamespaces(Sema &S, 
//	//TypeDefinition ^Type
//	Mono::CIL::Type* Type) {
//	std::string Namespace = marshalString<E_UTF8>(Type->getNamespace());
//	return findCreateNamespaces(S, Namespace);
//}

static AccessSpecifier convertMethodAccess(
  //MethodDefinition ^Method
  Mono::CIL::Method *Method) {
  if (Method->isPublic()) return AS_public;
  else if (Method->isAssembly()) return AS_internal;
  else if (Method->isFamily()) return AS_protected;
  else if (Method->isFamilyOrAssembly()) return AS_protected_public;
  else if (Method->isFamilyAndAssembly()) return AS_protected_private;
  else return AS_private;
}

static AccessSpecifier convertFieldAccess(
  //FieldDefinition ^Field
  Mono::CIL::Field* Field) {
  if (Field->isPublic()) return AS_public;
  else if (Field->isAssembly()) return AS_internal;
  else if (Field->isFamily()) return AS_protected;
  else if (Field->isFamilyOrAssembly()) return AS_protected_public;
  else if (Field->isFamilyAndAssembly()) return AS_protected_private;
  else return AS_private;
}

static AccessSpecifier convertPropertyAccess(Mono::CIL::Property* Prop){
  //PropertyDefinition ^Prop
  return AS_public;
}

static bool findCreateType(Sema &S, 
                           //TypeReference ^TypeRef,
                           Mono::CIL::Type* TypeRef,
                           QualType &Type,
                           CXXRecordDecl *MethodRecord = 0);

typedef Mono::Collections::Generic::Collection<Mono::Cecil::CustomAttribute^>
CustomAttributeCollection;

static void createDeclAttributes(Sema &S, 
                                 Mono::CIL::CILCustomAttributeHolder * Attributes,
                                 //CustomAttributeCollection ^Attributes,
                                 Decl *D);

static CXXRecordDecl *findCreateClassDecl(Sema &S, 
                                          //TypeDefinition ^TypeDef
                                          Mono::CIL::Type* TypeDef);

static bool hasCLIParamsAttribute(Sema &S, 
                                  //MethodDefinition ^Method
                                  Mono::CIL::Method* Method) {
  std::vector<Mono::CIL::Param*>* parvec = Method->getParams();
  //for each (ParameterDefinition ^Param in Method->Parameters) {
  for(int i=0;i<parvec->size();i++){
    Mono::CIL::CILCustomAttributeHolder * cah = parvec->at(i)->getCustomAttributes();
    //for each (CustomAttribute ^Attr in Param->getCustomAttributes()) {
    std::vector<CILCustomAttribute*> *cca = cah->getAttributes();
    for(int i=0;i<cca->size();i++){
      CXXRecordDecl *AttrClass =
        findCreateClassDecl(S, cca->at(i)->getAttributeType());
      if (AttrClass == S.getCLIContext()->ParamArrayAttribute)
        return true;
    }
  }
  return false;
}

static DeclarationName getMethodDeclName(Sema &S, 
                                         //MethodDefinition ^Method,
                                         Mono::CIL::Method *Method,
                                         CXXRecordDecl *RD) {
  ASTContext &C = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  std::string MethodName = Method->getName(); //marshalString<E_UTF8>(
  IdentifierInfo &II = IdentTable.get(MethodName);
  
  TagDecl *D = RD;
  
  if (RD->isCLIRecord() && RD->getCLIData()->isGeneric()) {
    /*Ty = S.getASTContext().getInjectedClassNameType(RD, */
    //D = RD->getDescribedClassTemplate();
  }
  
  DeclarationName DN;
  if (Method->isConstructor()) {
    CanQualType Ty = C.getCanonicalType(C.getTagDeclType(RD));
    DN = C.DeclarationNames.getCXXConstructorName(Ty);
  } else {
    DN = C.DeclarationNames.getIdentifier(&II);
  }
  
  return DN;
}

static CXXMethodDecl *findCreateMethod(Sema &S, 
                                       //MethodDefinition ^Method,
                                       Mono::CIL::Method *Method,
                                       CXXRecordDecl *RD,
                                       bool AddToDecl = true) {
  ASTContext &C = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  if (!RD) {
    RD = findCreateClassDecl(S, Method->declaringType());
    assert (RD && "Expected a valid record decl");
  }
  std::string name = Method->getFullName();
  bool lol=false;
  if(name.find("r.AppendFormat")!=std::string::npos)
    lol=true;
  
  DeclarationName DN = getMethodDeclName(S, Method, RD);
  
  unsigned MetadataToken = Method->MetadataToken();
  DeclContextLookupResult Res = RD->lookup(DN);
  for (auto it = Res.begin(); it != Res.end(); ++it) {
    Decl *D = *it;
    if (CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(D)) {
      CLIMethodData *CLIData = MD->getCLIData();
      if (CLIData->MetadataToken == MetadataToken)
        return MD;
    }
  }
  
  QualType RT;
  findCreateType(S, Method->returnType(), RT, RD);
  if (RT.isNull())
    return 0;
  //assert(!RT.isNull() && "Expected a valid method return type");
  
  llvm::SmallVector<QualType, 4> ParamTypes;
  std::vector<Mono::CIL::Param*>* parvec = Method->getParams();
  for(int i=0;i<parvec->size();i++){
    //for each (ParameterDefinition ^Param in Method->Parameters) {
    Mono::CIL::Param * aux = parvec->at(i);
    QualType ParamType;
    if (!findCreateType(S, aux->getTypeInfo(), ParamType, RD))
      return nullptr;
    
    if (ParamType.isNull())
      return nullptr;
    
    ParamTypes.push_back(ParamType);
  }
  
  FunctionProtoType::ExtProtoInfo Info;
  
  if (Method->isVarArgCall()) {
    Info.Variadic = true;
	std::vector<Mono::CIL::Param*> *parvec = Method->getParams();
  }
  
  QualType FT = C.getFunctionType(RT, ParamTypes, Info);
  
  TypeSourceInfo *TSI = C.getTrivialTypeSourceInfo(FT);
  FunctionProtoTypeLoc FTL = TSI->getTypeLoc().castAs<FunctionProtoTypeLoc>();
  DeclarationNameInfo DNI(DN, SourceLocation());
  
  CXXMethodDecl *MD = 0;
  if (Method->isStatic() && Method->isConstructor()) {
    return 0;
  } else if (Method->isConstructor()) {
    MD = CXXConstructorDecl::Create(C, RD, SourceLocation(), DNI, FT, TSI,
                                    /*IsExplicit=*/true, /*IsInline=*/false, /*IsImplicit=*/false,
                                    /*IsConstexpr=*/false);
  } else {
    MD = CXXMethodDecl::Create(C, RD, SourceLocation(), DNI, FT, TSI,
                               Method->isStatic() ? SC_Static : SC_None, /*IsInline=*/false,
                               /*IsConstexpr=*/false, SourceLocation());
  }
  
  CLIMethodData *CLIData = new (C) CLIMethodData();
  CLIData->MetadataToken = MetadataToken;
  CLIData->FullName = Method->getFullName(); //marshalString<E_UTF8>(
  
  MD->setCLIData(CLIData);
  MD->setAccess(convertMethodAccess(Method));
  
  llvm::SmallVector<ParmVarDecl*, 4> ParamDecls;
  unsigned paramIndex = 0;
  for(int i=0;i<parvec->size();i++){
    //for each (ParameterDefinition ^Param in Method->Parameters) {
    Mono::CIL::Param * aux = parvec->at(i);
    std::string ParamName = aux->getName(); //marshalString<E_UTF8>(
    IdentifierInfo& PII = IdentTable.get(ParamName);
    
    QualType ParamType;
    findCreateType(S, aux->getTypeInfo(), ParamType, RD);
    
    ParmVarDecl *PVD = ParmVarDecl::Create(C, MD, SourceLocation(),
                                           SourceLocation(), &PII, ParamType,
                                           C.getTrivialTypeSourceInfo(ParamType),
                                           SC_Auto, 0);
    
    assert(PVD && "Expected a valid parameter decl");
    PVD->setScopeInfo(0, paramIndex);
    FTL.setParam(paramIndex++, PVD);
    
    createDeclAttributes(S, aux->getCustomAttributes(), PVD);
    
    ParamDecls.push_back(PVD);
  }
  
  createDeclAttributes(S, Method->getCustomAttributes(), MD);
  // Method->paramcount() vvv
  assert(ParamDecls.size() == parvec->size());
  MD->setParams(ParamDecls);
  
  if (AddToDecl)
    RD->addDecl(MD);
  
  return MD;
}

static DeclaratorDecl *createField(Sema &S, 
                                   //FieldDefinition ^Field,
                                   Mono::CIL::Field * Field,
                                   CXXRecordDecl *RD) {
  ASTContext &C = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  std::string FieldName = Field->getName(); //marshalString<E_UTF8>(
  IdentifierInfo &II = IdentTable.get(FieldName);
  
  QualType FT;
  findCreateType(S, Field->fieldType(), FT, RD);
  
  if (FT.isNull()) {
    std::string Name = Field->fieldType()->getName(); //marshalString<E_UTF8>(
    return 0;
  }
  
  TypeSourceInfo *TSI = C.getTrivialTypeSourceInfo(FT);
  DeclaratorDecl *DD = 0;
  
  if (Field->isStatic()) {
    DD = VarDecl::Create(C, RD, SourceLocation(), SourceLocation(), &II,
                         FT, TSI, SC_Static);
  } else {
    DD = FieldDecl::Create(C, RD, SourceLocation(), SourceLocation(), &II,
                           FT, TSI, 0, 0, ICIS_NoInit);
  }
  
  assert(DD && "Expected a valid declarator decl");
  DD->setAccess(convertFieldAccess(Field));
  
  return DD;
}

static CLIRecordType GetCLIRecordType(
  //TypeDefinition ^Type
  Mono::CIL::Type *Type
  ) {
  assert(Type->isClass());
  if (Type->isInterface())
    return CLI_RT_InterfaceType;
  else if (Type->isValueType())
    return CLI_RT_ValueType;
  return CLI_RT_ReferenceType;
}

static CXXRecordDecl * findCreateClassDecl(Sema &S, 
                                           //TypeReference ^TypeRef
                                           Mono::CIL::Type* TypeRef);

static CLIDefinitionData *GetCLIRecordData(Sema &S, 
                                           Mono::CIL::Type* TypeDef
                                           //TypeDefinition^ TypeDef
  ) {
  CLIDefinitionData *CD = new (S.getASTContext()) CLIDefinitionData();
  CD->AssemblyName = TypeDef->getModule()->getAssembly()->getName(); //marshalString<E_UTF8>(
  CD->FullName = TypeDef->getFullName(); //marshalString<E_UTF8>(
  CD->Type = CLI_RT_ReferenceType;
  
  if (TypeDef->isInterface())
    CD->Type = CLI_RT_InterfaceType;
  else if (TypeDef->isValueType())
    CD->Type = CLI_RT_ValueType;
  
  return CD;
}

static ClassTemplateDecl *GetCLIClassTemplate(Sema &S, 
                                              //TypeDefinition^ TypeDef,
                                              Mono::CIL::Type *TypeDef,
                                              CXXRecordDecl *RD) {
  assert(TypeDef->hasGenericParameters());
  
  ASTContext &C = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  std::string Name = TypeDef->getName(); //marshalString<E_UTF8>(
  IdentifierInfo &II = IdentTable.get(Name);
  
  CLIGenericData *Data = new (C) CLIGenericData();
  llvm::SmallVector<TemplateTypeParmDecl *, 4> Params;
  
  //for each(GenericParameter ^Param in TypeDef->GenericParameters) {
  std::vector<Mono::CIL::GenericParam*>*gpvec = TypeDef->getGenericParameter();
  for(int i=0;i<gpvec->size();i++){
    Mono::CIL::GenericParam* Param = gpvec->at(i);
    CLIGenericParameter GP;
    GP.Name = Param->getName(); //marshalString<E_UTF8>(
    GP.Flags = 0;
    Data->Parameters.push_back(GP);
    
    if (Param->isTypeParameter() ) {
      TemplateTypeParmDecl *TP = TemplateTypeParmDecl::Create(C,
                                                              C.getTranslationUnitDecl(), SourceLocation(), SourceLocation(),
                                                              0, 0, &IdentTable.get(GP.Name), false, false);
      
      Params.push_back(TP);
    } else if (Param->isMethodParameter() ) {
      llvm_unreachable("Method template parameters not supported yet");
    }
  }
  
  RD->getCLIData()->setGenericData(Data);
  
  TemplateParameterList *TPL = TemplateParameterList::Create(C,
                                                             RD->getLocation(), SourceLocation(),
                                                             reinterpret_cast<NamedDecl**>(Params.data()), Params.size(),
                                                             SourceLocation());
  
  DeclContext *NS = findCreateNamespaces(S, TypeDef);
  ClassTemplateDecl *TD = ClassTemplateDecl::Create(C, NS, SourceLocation(),
                                                    &II, TPL, RD, /*PrevDecl=*/0);
  RD->setDescribedClassTemplate(TD);
  
  RD->setTypeForDecl(0);
  QualType T = TD->getInjectedClassNameSpecialization();
  T = C.getInjectedClassNameType(RD, T);
  
  return TD;
}

static CLIRecordDecl * createClass(Sema &S, Mono::CIL::Type * TypeDef){
  //TypeDefinition^ TypeDef) {
  ASTContext &C = S.getASTContext();
  std::string Name = TypeDef->getName(); //marshalString<E_UTF8>(
  
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  IdentifierInfo &II = IdentTable.get(Name);
  
  DeclContext *NS = findCreateNamespaces(S, TypeDef);
  if (!NS) return nullptr;
  
  CLIRecordDecl *RD = CLIRecordDecl::Create(C, TTK_RefClass, NS, SourceLocation(),
                                            SourceLocation(), &II, 0);
  
  RD->setCLIData(GetCLIRecordData(S, TypeDef));
  RD->startDefinition();
  
  if (TypeDef->hasGenericParameters()) {
    ClassTemplateDecl *TD = GetCLIClassTemplate(S, TypeDef, RD);
    NS->getPrimaryContext()->addDecl(TD);
  } else {
    NS->getPrimaryContext()->addDecl(RD);
  }
  
  return RD;
}

static CLICustomAttribute* createAttribute(Sema &S, 
                                           //CustomAttribute ^AttrDef
                                           Mono::CIL::CILCustomAttribute *AttrDef) {
  ASTContext &C = S.getASTContext();
  
  CXXRecordDecl *AttrClass = findCreateClassDecl(S, AttrDef->getAttributeType());
  if (!AttrClass) return 0;
  
  CXXMethodDecl *AttrCtor = findCreateMethod(S, AttrDef->getConstructor(),
                                             AttrClass);
  
  CLICustomAttribute *Attr = new(C) CLICustomAttribute(SourceRange(), C,
                                                       AttrClass, AttrCtor);
  
  if (AttrDef->hasConstructorArguments()) {
    //for each (CustomAttributeArgument Arg in AttrDef->ConstructorArguments) {
    std::vector<Mono::CIL::Param*> *parvec = AttrDef->getConstructorArguments();
    //TODO: investigate further
    for(int i=0;i<parvec->size();i++){
      CLICustomAttribute::Argument A;
      //A.Expression = Arg.Type;
      Attr->Arguments.push_back(A);
    }
  }
  
  if (AttrDef->hasFields()) {
    //for each (CustomAttributeNamedArgument Arg in AttrDef->Fields) {
    std::vector<Mono::CIL::Field*> *fldvec = AttrDef->getFields();
    for(int i=0;i<fldvec->size();i++){
      CLICustomAttribute::Argument A;
      A.Name = fldvec->at(i)->getName(); // marshalString<E_UTF8>(
      //A.Expression = Arg.Type;
      Attr->Arguments.push_back(A);
    }
  }
  
  if (AttrDef->hasProperties()) {
    //for each (CustomAttributeNamedArgument Arg in AttrDef->Properties) {
    std::vector<Mono::CIL::Property*> *propvec = AttrDef->getProperties();
    for(int i=0;i<propvec->size();i++){
      Mono::CIL::Property* Arg = propvec->at(i);
      CLICustomAttribute::Argument A;
      A.Name = Arg->getName(); //marshalString<E_UTF8>(
      //A.Expression = Arg.Type;
      Attr->Arguments.push_back(A);
    }
  }
  
  return Attr;
}

static void createDeclAttributes(Sema &S, 
                                 //CustomAttributeCollection ^Attributes,
                                 Mono::CIL::CILCustomAttributeHolder* Attributes,
                                 Decl *D) {
  std::vector<Mono::CIL::CILCustomAttribute*> *cavec = Attributes->getAttributes();
  //for each (CustomAttribute ^Attr in Attributes) {
  for(int i=0;i<cavec->size();i++){
    CILCustomAttribute* Attr = cavec->at(i);
    CLICustomAttribute *CLIAttr = createAttribute(S, Attr);
    D->addAttr(CLIAttr);
  }
}

static void createClassBases(Sema &S, 
                             Mono::CIL::Type* TypeDef,
                             //TypeDefinition ^TypeDef,
                             CXXRecordDecl *RD) {
  ASTContext &C = S.getASTContext();
  if (TypeDef->getBaseType() != NULL) {
    if (CLIRecordDecl *BRD = findCreateClassDecl(S, TypeDef->getBaseType())) {
      QualType BaseType = C.getTypeDeclType(BRD);
      CXXBaseSpecifier *Base = new (C) CXXBaseSpecifier(SourceRange(), false,
                                                        false, AS_public, C.getTrivialTypeSourceInfo(BaseType), SourceLocation());
      RD->setBases(&Base, 1);
    }
  }
  std::vector<Mono::CIL::Type*> *interfacevec = TypeDef->getInterfaces();
  //for each (TypeReference ^Interface in TypeDef->Interfaces) {
  for(int i=0;i<interfacevec->size();i++){
    if (CLIRecordDecl *BRD = findCreateClassDecl(S,interfacevec->at(i))) {
      QualType BaseType = C.getTypeDeclType(BRD);
      CXXBaseSpecifier *Base = new (C) CXXBaseSpecifier(SourceRange(), false,
                                                        false, AS_public, C.getTrivialTypeSourceInfo(BaseType), SourceLocation());
      RD->getCLIData()->Interfaces.push_back(Base);
    }
  }
}

static void createClassMethods(Sema &S, Mono::CIL::Type *TypeDef,
                               //TypeDefinition ^TypeDef,
                               CXXRecordDecl *RD) {
  std::vector<Mono::CIL::Method*> *metvec = TypeDef->getMethods();
  //for each (MethodDefinition ^Method in TypeDef->getMethods()) {
  for(int i=0;i<metvec->size();i++){
    if (metvec->at(i)->getName().length() == 0)
      continue;
    
    if (metvec->at(i)->isGetter() || metvec->at(i)->isSetter())
      continue;
    
    FunctionDecl *FD = findCreateMethod(S, metvec->at(i), RD);
  }
}

static void createClassFields(Sema &S, 
                              //TypeDefinition ^TypeDef,
                              Mono::CIL::Type* TypeDef,
                              CXXRecordDecl *RD) {
  std::vector<Mono::CIL::Field*> *fieldvec = TypeDef->getFields();
  //for each (FieldDefinition ^Field in TypeDef->Fields) {
  for(int i=0;i<fieldvec->size();i++){
    if (fieldvec->at(i)->getName().length()==0)
      continue;
    
    if (DeclaratorDecl *DD = createField(S, fieldvec->at(i), RD))
      RD->addDecl(DD);
  }
}

static void createClassProperties(Sema &S, 
                                  //TypeDefinition ^TypeDef,
                                  Mono::CIL::Type* TypeDef,
                                  CXXRecordDecl *RD) {
  ASTContext &C = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  std::vector<Mono::CIL::Property*> *propvec = TypeDef->getProperties();
  //for each (PropertyDefinition ^PropDef in TypeDef->Properties) {
  for(int i=0;i<propvec->size();i++){
    if (propvec->at(i)->getName().length()==0)
      continue;
    
    std::string Name = propvec->at(i)->getName(); //marshalString<E_UTF8>(
    IdentifierInfo &II = IdentTable.get(Name);
    DeclarationName DN = C.DeclarationNames.getIdentifier(&II);
    
    QualType PropTy;
    if (!findCreateType(S, propvec->at(i)->getPropertyType(), PropTy, RD))
      continue;
    
    CLIPropertyDecl *PD = CLIPropertyDecl::Create(S.getASTContext(),
                                                  RD->getPrimaryContext(), DN, PropTy);
    
    if (propvec->at(i)->hasParameters()) {
      std::vector<Mono::CIL::Param*> *parvec = propvec->at(i)->getParameters();
      //for each (PropertyDefinition ^PropDef in TypeDef->Properties) {
      for(int i=0;i<parvec->size();i++){
        //for each (ParameterDefinition ^Param in PropDef->Parameters) {
        QualType IndexTy;
        findCreateType(S, parvec->at(i)->getTypeInfo(), IndexTy, RD);
        PD->IndexerTypes.push_back(IndexTy);
      }
    }
    
    PD->setAccess(convertPropertyAccess( propvec->at(i)));
    
    if (!propvec->at(i)->getMethod()->isNull())
      PD->GetMethod = findCreateMethod(S,  propvec->at(i)->getMethod(), RD,
                                       /*AddToDecl=*/false);
    
    if (!propvec->at(i)->setMethod()->isNull())
      PD->SetMethod = findCreateMethod(S, propvec->at(i)->setMethod(), RD,
                                       /*AddToDecl=*/false);
    
    createDeclAttributes(S,propvec->at(i)->getCustomAttributes(), PD);
    RD->addDecl(PD);
  }
}

static void createClassImplicitOperator(Sema &S, 
                                        //TypeDefinition ^TypeDef,
                                        Mono::CIL::Type* TypeDef,
                                        CXXRecordDecl *RD,
                                        OverloadedOperatorKind Op) {
  ASTContext &C = S.getASTContext();
  
  QualType ClassTy = C.getHandleType(C.getRecordType(RD));
  llvm::SmallVector<QualType, 1> ParamTypes;
  ParamTypes.push_back(ClassTy);
  
  QualType ReturnTy = C.BoolTy;
  
  FunctionProtoType::ExtProtoInfo Info;
  QualType FunctionTy = C.getFunctionType(ReturnTy, ParamTypes, Info);
  
  TypeSourceInfo *TSI = C.getTrivialTypeSourceInfo(FunctionTy);
  FunctionProtoTypeLoc FTL = TSI->getTypeLoc().castAs<FunctionProtoTypeLoc>();
  
  DeclarationName DN = C.DeclarationNames.getCXXOperatorName(Op);
  DeclarationNameInfo DNI(DN, SourceLocation());
  
  CXXMethodDecl *MD = CXXMethodDecl::Create(C, RD, SourceLocation(),
                                            DNI, FunctionTy, TSI, SC_Auto, /*IsInline=*/false,
                                            /*IsConstexpr=*/false, SourceLocation());
  
  MD->setImplicit(true);
  
  llvm::SmallVector<StringRef, 1> ParamNames;
  ParamNames.push_back("rhs");
  
  llvm::SmallVector<ParmVarDecl*, 2> ParamDecls;
  for (unsigned i = 0; i < ParamNames.size(); ++i) {
    StringRef ParamName = ParamNames[i];
    IdentifierInfo &PII = S.getPreprocessor().getIdentifierTable().
      get(ParamName);
    
    QualType ParamType = ClassTy;
    ParmVarDecl *PVD = ParmVarDecl::Create(C, MD, SourceLocation(),
                                           SourceLocation(), &PII, ParamType,
                                           C.getTrivialTypeSourceInfo(ParamType), SC_Auto, 0);
    
    assert(PVD && "Expected a valid parameter decl");
    PVD->setScopeInfo(0, i);
    FTL.setParam(i++, PVD);
    
    ParamDecls.push_back(PVD);
  }
  
  MD->setParams(ParamDecls);
  
  RD->addDecl(MD);
}

static void createClassImplicitOperators(Sema &S, 
                                         Mono::CIL::Type* TypeDef,
                                         //TypeDefinition ^TypeDef,
                                         CXXRecordDecl *RD) {
  // 15.8.1 Handle equality operators
  // Every ref class type and value class type C implicitly provides the
  // following predefined equality operators:
  //
  //    bool operator ==(C^ x, C^ y); 
  //    bool operator !=(C^ x, C^ y);
  
  createClassImplicitOperator(S, TypeDef, RD, OO_EqualEqual);
  createClassImplicitOperator(S, TypeDef, RD, OO_ExclaimEqual);
}

static void createClassDecls(Sema &S, 
                             //TypeDefinition ^TypeDef, CXXRecordDecl *RD) {
                             Mono::CIL::Type* TypeDef, CXXRecordDecl *RD) {
  if(TypeDef->getName().find("StringB")!=std::string::npos)
	  TypeDef->getName();
  createClassBases(S, TypeDef, RD);
  createClassMethods(S, TypeDef, RD);
  createClassFields(S, TypeDef, RD);
  createClassProperties(S, TypeDef, RD);
  createClassImplicitOperators(S, TypeDef, RD);
  
  RD->completeDefinition();
}

static CXXRecordDecl * findCreateClassDecl(Sema &S, Mono::CIL::Type* TypeDef) {
  std::string name = TypeDef->getFullName();
  const char * nname = name.c_str();
  if (!TypeDef->hasClass()) return 0;
  Mono::CIL::Type * TheType = TypeDef;
  if(TypeDef->isGenericInstance())
	  TheType = TypeDef->getGenericClass();
  if(name.find("ric.List")!=std::string::npos)
	  int i = 0;
  DeclContext *NS = findCreateNamespaces(S, TheType);
  if (!NS) return 0;
  
  IdentifierInfo *II = getIdentifier(S, TheType->getName());
  DeclContextLookupResult Res = NS->lookup(II);
  
  for (auto it = Res.begin(); it != Res.end(); ++it) {
    Decl *D = *it;
    if (CLIRecordDecl *RD = dyn_cast<CLIRecordDecl>(D)) {
      return RD;
    } else if (ClassTemplateDecl *CTD = dyn_cast<ClassTemplateDecl>(D)) {
      CXXRecordDecl *TD = CTD->getTemplatedDecl();
      if (TD->isCLIRecord())
        return TD;
    }
  }
  
  // If we do not find the type, then it has not been found yet and we need
  // to create it explicitly.
  
  CXXRecordDecl *RD = createClass(S, TheType);
  createClassDecls(S, TheType, RD);
  
  return RD;
}

//static CXXRecordDecl * findCreateClassDecl(Sema &S, Mono::CIL::Type *TypeRef) {
//	TypeDefinition ^TypeDef = TypeRef->Resolve();
//	return findCreateClassDecl(S, TypeDef);
//}

static bool convertPrimitiveType(Sema &S, Mono::CIL::Type* TypeRef, QualType &Type) {
  ASTContext& C = S.getASTContext();
  Mono::CIL::Type *TypeDef = TypeRef;
  if(TypeRef->isArray())
	  TypeDef = TypeRef->getArrayType();
  //TypeDefinition ^TypeDef = TypeRef->Resolve();
  //if (!TypeRef->hasClass())
  //	return false;
  
  int Hash = llvm::HashString(TypeDef->getFullName()); //marshalString<E_UTF8>(
  
  CLIPrimitiveTypes &P = S.getCLIContext()->Types;
  
  if (Hash == P.Void.Hash) {
    Type = C.VoidTy;
    return true;
  } else if (Hash == P.Boolean.Hash) {
    Type = C.BoolTy;
    return true;
  } else if (Hash == P.Char.Hash) {
    Type = C.WCharTy;
    return true;
  } else if (Hash == P.Byte.Hash) {
    Type = C.UnsignedCharTy;
    return true;
  } else if (Hash == P.SByte.Hash) {
    // FIXME: Check for modopt IsSignUnspecifiedByte
    Type = C.CharTy;
    return true;
  } else if (Hash == P.Int16.Hash) {
    Type = C.ShortTy;
    return true;
  } else if (Hash == P.UInt16.Hash) {
    Type = C.UnsignedShortTy;
    return true;
  } else if (Hash == P.Int32.Hash) {
    // FIXME: Check for modopt IsLong
    Type = C.IntTy;
    return true;
  } else if (Hash == P.UInt32.Hash) {
    // FIXME: Check for modopt IsLong
    Type = C.UnsignedIntTy;
    return true;
  } else if (Hash == P.Int64.Hash) {
    Type = C.LongLongTy;
    return true;
  } else if (Hash == P.UInt64.Hash) {
    Type = C.UnsignedLongLongTy;
    return true;
  } else if (Hash == P.Single.Hash) {
    Type = C.FloatTy;
    return true;
  } else if (Hash == P.Double.Hash) {
    // FIXME: Check for modopt IsLong
    Type = C.DoubleTy;
    return true;
  } else if (Hash == P.String.Hash) {
    Type = P.String.Ty;
    return true;
  } else if (Hash == P.IntPtr.Hash) {
    Type = P.IntPtr.Ty;
    return true;
  } else if (Hash == P.UIntPtr.Hash) {
    Type = P.UIntPtr.Ty;
    return true;
  }
  
  return false;
}

static void createClassGenericParameters(Sema &S, CXXRecordDecl *RD,
                                         Mono::CIL::Type* Type) {
  int i=0;
  if(!Type->isGenericInstance()) return;
  if(Type->hasGenericClass())
    i=1;
  std::vector<Mono::CIL::GenericParam*>* gpvec = Type->getGenericParameter();
  //for each(GenericParameter ^Param in Type->getGenericParameters()) {
  //TODO: genericParam + genericArguments
  for(int i=0;i<gpvec->size();i++){
    std::string Name = gpvec->at(i)->getName(); //marshalString<E_UTF8>(
    //Console::WriteLine("{0} {1}", Param->FullName, Param->Name);
    continue;
  }
  
  //for each(TypeReference ^Arg in Type->GenericArguments) {
  //	std::string Name = marshalString<E_UTF8>(Arg->Name);
  //Console::WriteLine("{0} {1}", Arg->FullName, Arg->Name);
  //	continue;
  //}
  
  // Demangle the CLI generic name.
  //std::string Name = Type->getName(); // marshalString<E_UTF8>(
  //Name = Name.substr(0, Name.find("`"));
}

static bool findCreateType(Sema &S, Mono::CIL::Type* TypeRef, QualType &Type,
                           CXXRecordDecl *MethodRecord) {
  if (convertPrimitiveType(S, TypeRef, Type))
    return true;
  
  ASTContext &Context = S.getASTContext();
  
  if (TypeRef->isArray()) {
    //Mono::Cecil::ArrayType ^Arr = safe_cast<Mono::Cecil::ArrayType^>(TypeRef);
    QualType ElementType;
    if (!findCreateType(S, TypeRef->getArrayType(), ElementType, MethodRecord))
      return false;
    CXXRecordDecl *RD = findCreateClassDecl(S, TypeRef->getArrayType());
    Type = Context.getHandleType(Context.getCLIArrayType(ElementType,
                                                         TypeRef->getArrayRank(), S.getCLIContext()->Types.Array.Decl));
    return true;
  } else if (TypeRef->isGenericParameter()) {
    assert(MethodRecord && "Expected a valid C++/CLI record");
    
    ClassTemplateDecl *TD = MethodRecord->getDescribedClassTemplate();
    if (!TD) {
      Type = Context.VoidTy;
      return false;
    }
    
    assert(TD && "Expected a valid class template");
    std::string Name = TypeRef->getName(); //marshalString<E_UTF8>(
    
    TemplateParameterList *TPL = TD->getTemplateParameters();
    for (unsigned I = 0, E = TPL->size(); I != E; ++I) {
      NamedDecl *TP = TPL->getParam(I);
      
      TemplateTypeParmDecl *TT = dyn_cast<TemplateTypeParmDecl>(TP);
      assert(TT && "Expected a template type parameter");
      
      if (TP->getName() == Name) {
        Type = Context.getTemplateTypeParmType(0, I, 0, TT);
        return true;
      }
    }
  } else {
    if (CXXRecordDecl *RD = findCreateClassDecl(S, TypeRef)) {
      if (TypeRef->isGenericInstance()) {
        //GenericInstanceType ^Instance = safe_cast<GenericInstanceType^>(TypeRef);
        createClassGenericParameters(S, RD, TypeRef);
        Type = Context.getHandleType(Context.getRecordType(RD));
        return true;
      }
      Type = Context.getHandleType(Context.getRecordType(RD));
      return true;
    }
  }
  
  //llvm_unreachable("Unhandled managed type");
  Type = Context.VoidTy;
  return false;
}

static void initializeCLIType(Sema &S, CLIPrimitiveType &P, CLITypeKind Kind,
                              //TypeDefinition ^Type) {
                              Mono::CIL::Type * Type){
  using namespace clix;
  
  P.Hash = llvm::HashString(Type->getFullName()); //marshalString<E_UTF8>(
  P.Token = Type->getMetadataToken();
  P.Decl = createClass(S, Type);
  P.Decl->getCLIData()->Kind = Kind;
  
  QualType RT = S.getASTContext().getRecordType(P.Decl);
  
  if (Type->isValueType())
    P.Ty = RT;
  else
    P.Ty = S.getASTContext().getHandleType(RT);
}

static void initializeCLIClass(Sema &S, CLIPrimitiveType &P,
                               //TypeDefinition ^Type) {
                               Mono::CIL::Type * Type){
  createClassDecls(S, Type, P.Decl);
}

//static void initializeCLITypes(Sema &S, AssemblyDefinition^ Assembly) {
static void initializeCLITypes(Sema &S, Mono::CIL::Assembly* Assembly) {
  Mono::CIL::Module *Module = Assembly->getMainModule();
  CLIPrimitiveTypes &P = S.getCLIContext()->Types;
  
  // Get the metadata tokens for each type so we can look it up later.
#define CLI_TYPE(X) \
  initializeCLIType(S, P.X, CLI_TK_None, Module->getType("System."#X));
#define CLI_PRITIMIVE_TYPE(X) \
  initializeCLIType(S, P.X, CLI_TK_##X, Module->getType("System."#X));
#include "clang/AST/CLITypes.def"
#undef CLI_TYPE
#undef CLI_PRITIMIVE_TYPE
  
#define CLI_TYPE(X) \
  initializeCLIClass(S, P.X, Module->getType("System."#X));
#include "clang/AST/CLITypes.def"
#undef CLI_TYPE
  
  CLISemaContext &Ctx = *S.getCLIContext();
  
  Ctx.DefaultMemberAttribute = findCreateClassDecl(S,
                                                   Module->getType("System.Reflection.DefaultMemberAttribute"));
  
  Ctx.ParamArrayAttribute = findCreateClassDecl(S,
                                                Module->getType("System.ParamArrayAttribute"));
  
  Ctx.IEnumerable = findCreateClassDecl(S,
                                        Module->getType("System.Collections.IEnumerable"));
  
  Ctx.GenericIEnumerable = findCreateClassDecl(S,
                                               Module->getType("System.Collections.Generic.IEnumerable`1"));
}

static NamespaceDecl *initializeNamespaceDecl(Sema &S) {
  ASTContext &ASTContext = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  TranslationUnitDecl *TU = ASTContext.getTranslationUnitDecl();
  
  NamespaceDecl *Namespace = NamespaceDecl::Create(ASTContext,
                                                   TU->getPrimaryContext(), /*IsInline=*/false, SourceLocation(),
                                                   SourceLocation(), &IdentTable.get("cli"), 0);
  Namespace->setImplicit(true);
  TU->addDecl(Namespace);
  
  return Namespace;
}

static ClassTemplateDecl *initializeCLIArrayDecl(Sema &S,
                                                 NamespaceDecl *Namespace) {
  ASTContext &ASTContext = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  CXXRecordDecl *RD = CXXRecordDecl::Create(ASTContext, TTK_RefClass,
                                            Namespace->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                            &IdentTable.get("array"), 0, false);
  
  RD->startDefinition();
  RD->completeDefinition();
  
  // Set System::Array as the base class.
  QualType BaseType = ASTContext.getTypeDeclType(S.getCLIContext()->
                                                 Types.Array.Decl);
  CXXBaseSpecifier *Base = new (ASTContext) CXXBaseSpecifier(SourceRange(),
                                                             false, false, AS_public, ASTContext.getTrivialTypeSourceInfo(BaseType),
                                                             SourceLocation());
  RD->setBases(&Base, 1);
  
  TemplateTypeParmDecl *TT = TemplateTypeParmDecl::Create(ASTContext,
                                                          RD->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                                          0, 0, &IdentTable.get("T"), /*Typename=*/true, /*ParameterPack=*/false);
  
  NonTypeTemplateParmDecl *NT = NonTypeTemplateParmDecl::Create(ASTContext,
                                                                RD->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                                                0, 0, &IdentTable.get("Rank"), ASTContext.UnsignedIntTy, false,
                                                                ASTContext.getTrivialTypeSourceInfo(ASTContext.UnsignedIntTy));
  NT->setDefaultArgument(IntegerLiteral::Create(ASTContext,
                                                llvm::APInt(32, 1), ASTContext.UnsignedIntTy, SourceLocation()), false);
  
  NamedDecl *TemplateDecls[] = { TT, NT };
  TemplateParameterList *TPL = TemplateParameterList::Create(ASTContext,
                                                             SourceLocation(), SourceLocation(), TemplateDecls, 2, SourceLocation());
  
  ClassTemplateDecl *ClassTemplate = 
    ClassTemplateDecl::Create(ASTContext, Namespace->getPrimaryContext(),
                              SourceLocation(), DeclarationName(&IdentTable.get("array")), TPL,
                              RD, 0);
  
  Namespace->addDecl(ClassTemplate);
  
  return ClassTemplate;
}

static ClassTemplateDecl *initializeInteriorPtrDecl(Sema &S,
                                                    NamespaceDecl *Namespace) {
  ASTContext &ASTContext = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  CXXRecordDecl *RD = CXXRecordDecl::Create(ASTContext, TTK_Class,
                                            Namespace->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                            &IdentTable.get("interior_ptr"), 0, false);
  
  TemplateTypeParmDecl *TT = TemplateTypeParmDecl::Create(ASTContext,
                                                          RD->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                                          0, 0, &IdentTable.get("T"), /*Typename=*/true, false);
  
  NamedDecl *TemplateDecls[] = { TT };
  TemplateParameterList *TPL = TemplateParameterList::Create(ASTContext,
                                                             SourceLocation(), SourceLocation(), TemplateDecls, 1, SourceLocation());
  
  ClassTemplateDecl *ClassTemplate = 
    ClassTemplateDecl::Create(ASTContext, Namespace->getPrimaryContext(),
                              SourceLocation(), DeclarationName(&IdentTable.get("interior_ptr")), TPL,
                              RD, 0);
  Namespace->addDecl(ClassTemplate);
  
  return ClassTemplate;
}

static ClassTemplateDecl *initializePinPtrDecl(Sema &S,
                                               NamespaceDecl *Namespace) {
  ASTContext &ASTContext = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  CXXRecordDecl *RD = CXXRecordDecl::Create(ASTContext, TTK_Class,
                                            Namespace->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                            &IdentTable.get("pin_ptr"), 0, false);
  
  TemplateTypeParmDecl *TT = TemplateTypeParmDecl::Create(ASTContext,
                                                          RD->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                                          0, 0, &IdentTable.get("T"), /*Typename=*/true, false);
  
  NamedDecl *TemplateDecls[] = { TT };
  TemplateParameterList *TPL = TemplateParameterList::Create(ASTContext,
                                                             SourceLocation(), SourceLocation(), TemplateDecls, 1, SourceLocation());
  
  ClassTemplateDecl *ClassTemplate = 
    ClassTemplateDecl::Create(ASTContext, Namespace->getPrimaryContext(),
                              SourceLocation(), DeclarationName(&IdentTable.get("pin_ptr")), TPL,
                              RD, 0);
  Namespace->addDecl(ClassTemplate);
  
  return ClassTemplate;
}

static ClassTemplateDecl *initializeSafeCastDecl(Sema &S,
                                                 NamespaceDecl *Namespace) {
  ASTContext &ASTContext = S.getASTContext();
  IdentifierTable &IdentTable = S.getPreprocessor().getIdentifierTable();
  
  CXXRecordDecl *RD = CXXRecordDecl::Create(ASTContext, TTK_Class,
                                            Namespace->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                            &IdentTable.get("safe_cast"), 0, false);
  
  TemplateTypeParmDecl *TT = TemplateTypeParmDecl::Create(ASTContext,
                                                          RD->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                                          0, 0, &IdentTable.get("T"), /*Typename=*/true, false);
  
  NamedDecl *TemplateDecls[] = { TT };
  TemplateParameterList *TPL = TemplateParameterList::Create(ASTContext,
                                                             SourceLocation(), SourceLocation(), TemplateDecls, 1, SourceLocation());
  
  ClassTemplateDecl *ClassTemplate = 
    ClassTemplateDecl::Create(ASTContext, Namespace->getPrimaryContext(),
                              SourceLocation(), DeclarationName(&IdentTable.get("safe_cast")), TPL,
                              RD, 0);
  Namespace->addDecl(ClassTemplate);
  
  return ClassTemplate;
}

static void initializeCLINamespace(Sema &S) {
  CLISemaContext *Ctx = S.getCLIContext();
  
  assert(!Ctx->CLINamespace && "Expected unitialized CLI namespace");
  NamespaceDecl *Namespace = initializeNamespaceDecl(S);
  Ctx->CLINamespace = Namespace;
  
  // C++/CLI provides a couple of declarations in the ::cli namespace.
  //  array, interior_ptr, pin_ptr, or safe_cast
  
  assert(!Ctx->Array && "Expected unitialized CLI array decl");
  Ctx->Array = initializeCLIArrayDecl(S, Namespace);
  
  assert(!Ctx->InteriorPtr && "Expected unitialized CLI interior_ptr decl");
  Ctx->InteriorPtr = initializeInteriorPtrDecl(S, Namespace);
  
  assert(!Ctx->PinPtr && "Expected unitialized CLI pin_ptr decl");
  Ctx->PinPtr = initializePinPtrDecl(S, Namespace);
  
  assert(!Ctx->SafeCast && "Expected unitialized CLI safe_cast decl");
  Ctx->SafeCast = initializeSafeCastDecl(S, Namespace);
  
  ASTContext &ASTContext = S.getASTContext();
  TranslationUnitDecl *TU = ASTContext.getTranslationUnitDecl();
  UsingDirectiveDecl *UD = UsingDirectiveDecl::Create(ASTContext,
                                                      TU->getPrimaryContext(), SourceLocation(), SourceLocation(),
                                                      NestedNameSpecifierLoc(), SourceLocation(), Namespace,
                                                      Namespace->getParent());
  TU->addDecl(UD);
}

class CLICecilContext
{
public:
  gcroot<ReaderParameters^> ReaderParameters;
};

void Sema::LoadManagedAssembly(FileID FID) {
  SourceManager &SourceMgr = getSourceManager();
  
  const llvm::MemoryBuffer *Buffer = SourceMgr.getBuffer(FID);
  assert(Buffer && "Expected a valid buffer from file ID");
  const FileEntry *fe = SourceMgr.getFileEntryForID(FID);
  printf("%s\n",fe->getName());

  mono_init("mono");
  DumpAssemblyRefs(std::string(fe->getName()));
  void *Buf = (void*) Buffer->getBufferStart();
  size_t Size = Buffer->getBufferSize();
  
  array<Byte> ^Data = gcnew array<Byte>(Size);
  Marshal::Copy(IntPtr(Buf), Data, 0, Int32(Size)); 
  
  if (!CLIContext->CecilContext) {
    CLICecilContext *CecilContext = new CLICecilContext();
    CLIContext->CecilContext = CecilContext;
    
    ReaderParameters ^Parameters = gcnew ReaderParameters();
    Parameters->AssemblyResolver = gcnew DefaultAssemblyResolver();
    CecilContext->ReaderParameters = Parameters;
  }
  Mono::CIL::Assembly *Assembly = new Mono::CIL::Assembly(fe->getName());
  //AssemblyDefinition ^Assembly = AssemblyDefinition::ReadAssembly(
  //	gcnew MemoryStream(Data), CLIContext->CecilContext->ReaderParameters);
  
  assert(CLIContext && "Expected an initialized CLI context");
  
  //if (Assembly->Name->HasPublicKey) {
  if(Assembly->hasPublicKey()){
    //String^ Token = BitConverter::ToString(Assembly->Name->PublicKeyToken);
    std::string Token = Assembly->getPublicKeyToken();
    //TODO:
    //Token = Token->Replace("-", String::Empty)->ToLower();
    // Compare the assembly's public key token with that of mscorlib.
    // This token is the same in both Mono and Microsoft CLR.
    if (Token.find("b77a5c561934e089")!=std::string::npos && Assembly->getName().find("mscorlib")!=std::string::npos)
      initializeCLITypes(*this, Assembly);
    
    if (CLIContext->CLINamespace == 0)
      initializeCLINamespace(*this);
  }
  //int modules = 0;
  //	int typeNum = 0;
  std::vector<std::string>* typenamescecil = new std::vector<std::string>(); 
  //for each (ModuleDefinition ^Module in Assembly->Modules) {
  //modules++;
  Mono::CIL::Module* Mod = Assembly->getMainModule();
  //	for each (TypeDefinition ^TypeDef in Module->GetTypes()) {
  //std::string naux = ""; naux+= marshalString<E_UTF8>(TypeDef->Namespace);
  //naux+="."; naux+= marshalString<E_UTF8>(TypeDef->Name);
  //typenamescecil->push_back(std::string(naux));
  std::vector<Mono::CIL::Type*> *typevec = Mod->getTypes();
  for(int i=0;i<typevec->size();i++){
    QualType Type;
    findCreateType(*this, typevec->at(i), Type);
  }
  
  //	int i=0;
  //	std::map<std::string, int> filder;
  //	for(int i=0;i<typenamescecil->size();i++)
  //		filder[(*typenamescecil)[i]]++;
  //	printf("OURTYPES:\n",filder[(*typenames)[i]]);
  //	for(int i=0;i<typenames->size();i++){
  //		filder[(*typenames)[i]]++;
  //		if(filder[(*typenames)[i]]==1){
  //			printf("\t%s",(*typenames)[i].c_str());
  //		}
  //	}
  //	printf("THEIRTYPES:\n",filder[(*typenames)[i]]);
  //	for(int i=0;i<typenamescecil->size();i++)
  //		if(filder[(*typenamescecil)[i]]==1){
  //			printf("\t%s",(*typenamescecil)[i].c_str());
  //		}
}


/// C++/CLI conversion functions
static const CLIRecordDecl * getCLIRecordDeclForHandleType(QualType T) {
  if (const HandleType *PT = T->getAs<HandleType>())
    if (const RecordType *RT = PT->getPointeeType()->getAs<RecordType>())
      return dyn_cast<CLIRecordDecl>(RT->getDecl());
  return 0;
}

#pragma unmanaged

/// Helper function to determine whether this is C++/CLI string literal
/// conversion to a System::String^. (C++/CLI 14.2.5 String literal conversions)
static bool isCLIStringLiteralConversion(Expr *From, QualType ToType) {
  // Look inside the implicit cast, if it exists.
  if (ImplicitCastExpr *Cast = dyn_cast<ImplicitCastExpr>(From))
    From = Cast->getSubExpr();
  
  StringLiteral *StrLit = dyn_cast<StringLiteral>(From->IgnoreParens());
  if (!StrLit) return false;
  
  const CLIRecordDecl * RD = getCLIRecordDeclForHandleType(ToType);
  if (!RD) return false;
  
  switch (StrLit->getKind()) {
  case StringLiteral::UTF8:
  case StringLiteral::UTF16:
  case StringLiteral::UTF32:
  case StringLiteral::Ascii:
  case StringLiteral::Wide:
    return true;
  }
  
  return false;
}

static QualType ConvertBuiltinTypeToCLIPrimitiveType(Sema &S,
                                                     const BuiltinType *Builtin) {
  CLISemaContext *Ctx = S.getCLIContext();
  CLIPrimitiveTypes &Tys = Ctx->Types;
  
  // 8.2.1 Fundamental types and the CLI
  switch (Builtin->getKind()) {
  case BuiltinType::Bool: return Tys.Boolean.Ty;
  case BuiltinType::SChar: return Tys.SByte.Ty;
  case BuiltinType::UChar: return Tys.Byte.Ty;
  case BuiltinType::Char_S: return Tys.SByte.Ty;
  case BuiltinType::Char_U: return Tys.SByte.Ty;
  case BuiltinType::Short: return Tys.Int16.Ty;
  case BuiltinType::UShort: return Tys.UInt16.Ty;
  case BuiltinType::Int: return Tys.Int32.Ty;
  case BuiltinType::UInt: return Tys.UInt32.Ty;
  case BuiltinType::Long: return Tys.Int32.Ty;
  case BuiltinType::ULong: return Tys.UInt32.Ty;
  case BuiltinType::LongLong: return Tys.Int64.Ty;
  case BuiltinType::ULongLong: return Tys.UInt64.Ty;
  case BuiltinType::Float: return Tys.Single.Ty;
  case BuiltinType::Double: return Tys.Double.Ty;
  case BuiltinType::LongDouble: return Tys.Double.Ty;
  case BuiltinType::WChar_S: return Tys.Char.Ty;
  case BuiltinType::WChar_U: return Tys.Char.Ty;
  default: return QualType();
  }
  
  return QualType();
}

/// IsBoxingConversion - Determines whether the conversion from
/// FromType to ToType is a boxing conversion (C++/CLI 14.2.6).
bool IsBoxingConversion(Sema &S, QualType FromType, QualType ToType,
                        QualType &ConvertedType) {
  // "A boxing conversion involves the creation of a new object on the
  // CLI heap. A boxing conversion shall be applied only to instances of
  // value types, with the exception of pointers. For any given value
  // type V, the conversion results in a V^."
  if (!ToType->isHandleType())
    return false;
  
  CXXRecordDecl *RD = ToType->getPointeeType()->getAsCXXRecordDecl();
  if (!RD | !RD->isCLIRecord())
    return false;
  
  // Value Types: Fundamental Type, Enum, Pointer (not considered for
  // boxing purposes), Value Class
  if (const BuiltinType *FromBuiltin = FromType->getAs<BuiltinType>()) {
    QualType Ty = ConvertBuiltinTypeToCLIPrimitiveType(S, FromBuiltin);
    if (Ty.isNull())
      return false;
    ConvertedType = Ty;
    // Value types are not initialized as handles
    ConvertedType = S.getASTContext().getHandleType(ConvertedType);
  } else if (const RecordType *FromRecord = FromType->getAs<RecordType>()) {
    const CXXRecordDecl *FRD = FromRecord->getAsCXXRecordDecl();
    if (!FRD->isCLIRecord())
      return false;
    if (FRD->getCLIData()->Type != CLI_RT_ValueType)
      return false;
    CXXBasePaths P;
    if (!S.Context.hasSameType(ToType->getPointeeType(), FromType) &&
        !FRD->isDerivedFrom(RD, P))
      return false;
    ConvertedType = ToType;
  } else if (const EnumType *FromEnum = FromType->getAs<EnumType>()) {
    llvm_unreachable("Enum boxing conversions not implemented yet");
  } else {
    return false;
  }
  
  assert(!ConvertedType.isNull());
  if (RD == S.getCLIContext()->Types.Object.Decl)
    ConvertedType = S.getCLIContext()->Types.Object.Ty;
  
  return true;
}

// Used in SemaExprCXX.cpp
QualType GetBoxingConversionValueType(Sema &S, QualType FromType) {
  if (const BuiltinType *FromBuiltin = FromType->getAs<BuiltinType>()) {
    QualType Ty = ConvertBuiltinTypeToCLIPrimitiveType(S, FromBuiltin);
    assert(!Ty.isNull());
    return Ty;
  } else if (const RecordType *FromRecord = FromType->getAs<RecordType>()) {
    return FromType;
    //} else if (const EnumType *FromEnum = FromType->getAs<EnumType>()) {
  } else {
    assert(0 && "Expected a valid fundamental type");
  }
  
  return QualType();
}

/// CheckHandleConversion - Check the handle conversion from the
/// expression From to the type ToType. This routine checks for
/// ambiguous or inaccessible derived-to-base handle
/// conversions for which IsHandleConversion has already returned
/// true. It returns true and produces a diagnostic if there was an
/// error, or returns false otherwise.
bool Sema::CheckHandleConversion(Expr *From, QualType ToType,
                                 CastKind &Kind,
                                 CXXCastPath &BasePath,
                                 bool IgnoreBaseAccess) {
  QualType FromType = From->getType();
  
  if (FromType->isHandleType()) {
    // The conversion was successful.
    // FIXME: Check for accessibility
    Kind = CK_CLI_DerivedToBaseHandle;
    return false;
  }
  
  // We shouldn't fall into this case unless it's valid for other
  // reasons.
  if (From->isNullPointerConstant(Context, Expr::NPC_ValueDependentIsNull)) {
    Kind = CK_CLI_NullToHandle;
    return false;
  }
  
  return true;
}

ActionResult<CLICustomAttribute*> Sema::ActOnCLIAttribute(Scope *S,
                                                          CLIAttributeTarget Target,
                                                          SourceLocation TargetLoc,
                                                          StringRef AttributeName,
                                                          MultiExprArg AttrArgs) {
  bool isFileScope = S->GetDecls().size() == 1 && S->GetDecls().count(
    Context.getTranslationUnitDecl());
  
  //if (Target == CLI_AT_assembly && !isFileScope) {
  //  Diag(TargetLoc, Diags.getCustomDiagID(DiagnosticsEngine::Warning,
  //    "assembly attribute can only be used at file-scope"));
  //  return true;
  //}
  
  DeclarationNameInfo DeclName(PP.getIdentifierInfo(AttributeName),
                               SourceLocation());
  
  LookupResult Res(*this, DeclName, LookupTagName);
  if (!LookupName(Res, S)) {
    // If the lookup failed the first time, try again with "Attribute" added
    // to the end of the name.
    DeclName.setName(PP.getIdentifierInfo(AttributeName.str()+"Attribute"));
    Res.setLookupNameInfo(DeclName);
    LookupName(Res, S);
  }
  
  LookupResult::LookupResultKind Kind = Res.getResultKind();
  if (Kind != LookupResult::Found) {
    return true;
  }
  
  CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(Res.getFoundDecl());
  
  if (!RD || !RD->isCLIRecord()) {
    Diag(TargetLoc, Diags.getCustomDiagID(DiagnosticsEngine::Error,
                                          "attribute class is invalid"));
    return true;
  }
  
  CLICustomAttribute *Attr = new (Context) CLICustomAttribute(
    SourceRange(), Context, RD, /*FIXME: Ctor*/0);
  
  return Attr;
}

bool HasCLIParamArrayAttribute(Sema &S, const FunctionDecl *FD,
                               QualType &ParamType) {
  unsigned Params = FD->getNumParams();
  if (!Params)
    return false;
  
  auto PD = FD->getParamDecl(--Params);
  assert(PD && "Expected a valid parameter decl");
  
  for (auto it = PD->specific_attr_begin<CLICustomAttribute>();
       it != PD->specific_attr_end<CLICustomAttribute>(); ++it) {
    CLICustomAttribute *CLIAttr = *it;
    if (CLIAttr->Class == S.getCLIContext()->ParamArrayAttribute) {
      assert(isa<HandleType>(PD->getType()));
      ParamType = PD->getType();
      return true;
    }
  }
  
  return false;
}

Attr *Sema::InstantiateUnknownAttr(const Attr *At,
                                   const MultiLevelTemplateArgumentList &TemplateArgs) {
  switch (At->getKind()) {
  default: return 0;
  case attr::CLICustomAttribute: {
    const CLICustomAttribute *A = cast<CLICustomAttribute>(At);
    return A->clone(Context);
  }
  }
  
  return 0;
}


} // end namespace clang
